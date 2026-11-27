#!/usr/bin/env python3
"""Replay certified low-weight bases at the long precision needed by Sage Katz.

Only the weight-two q-expansion is extended directly. Higher weights replay
saved products, scaled Serre derivatives, and guarded local saturation.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import gzip
import hashlib
import json
from pathlib import Path
import time


WEIGHTS = (2,4,6)


def read_json(path):
    data = Path(path).read_bytes()
    return json.loads(gzip.decompress(data) if str(path).endswith(".gz") else data)


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    data = (json.dumps(value,sort_keys=True,separators=(",",":"))+"\n").encode()
    payload = gzip.compress(data,mtime=0) if path.suffix == ".gz" else data
    temporary = path.with_name(path.name+".tmp")
    temporary.write_bytes(payload)
    temporary.replace(path)
    return hashlib.sha256(data).hexdigest()


def raw_json_sha(path):
    data = Path(path).read_bytes()
    if str(path).endswith(".gz"):
        data = gzip.decompress(data)
    return hashlib.sha256(data).hexdigest()


def records_from(directory):
    records, hashes = {}, {}
    for weight in WEIGHTS:
        path = Path(directory)/f"M{weight}-basis.json.gz"
        record = read_json(path)
        if record["schema"] != "product-modular-basis-v1" or record["weight"] != weight:
            raise ArithmeticError("Wrong modular basis checkpoint schema or weight")
        if not record["five_saturated_q_lattice"] or record["pivot_selection_prime"] != 5:
            raise ArithmeticError("The long supplier requires certified 5-saturated short bases")
        if record["exact_rank"] != record["dimension"] or record["rank_mod5_after"] != record["dimension"]:
            raise ArithmeticError("The short basis was not fully certified")
        records[weight] = record
        hashes[str(weight)] = hashlib.sha256(path.read_bytes()).hexdigest()
    levels = {record["metadata"]["level"] for record in records.values()}
    if len(levels) != 1:
        raise ArithmeticError("Short basis levels do not agree")
    return records,hashes


class SavedBasisSupplier:
    """Callable with Sage's low_weight_generators(N,p,m,NN) signature.

    progress, when supplied, receives one JSON text string per event.
    """
    def __init__(self, checkpoint_dir, output_dir, progress=None,
                 maximum_guard=30, use_cache=True):
        self.checkpoint_dir = Path(checkpoint_dir)
        self.output_dir = Path(output_dir)
        self.progress = progress
        self.maximum_guard = int(maximum_guard)
        self.use_cache = use_cache
        self.started = time.monotonic()
        self.events = []
        self.records,self.hashes = records_from(self.checkpoint_dir)
        self.level = int(self.records[2]["metadata"]["level"])
        self.rounds = {k:len(self.records[k]["saturation_at_5_operations"])
                       for k in WEIGHTS}
        self.guard = sum(self.rounds.values())
        if self.guard > self.maximum_guard:
            raise ArithmeticError("Required saturation guard exceeds the explicit cap")

    def emit(self,stage,**data):
        event = {"stage":stage,"elapsed_seconds":time.monotonic()-self.started,**data}
        self.events.append(event)
        write_json(self.output_dir/"supplier-progress.json",self.events)
        message = json.dumps(event,sort_keys=True)
        if self.progress is None:
            print(message,flush=True)
        else:
            self.progress(message)

    def specification(self,N,p,m,NN):
        N,p,m,NN = map(int,(N,p,m,NN))
        if N != self.level or p != 5 or m < 1 or NN < 1:
            raise ValueError("Supplier level must match the checkpoints and prime must be5")
        return {"schema":"long-low-weight-request-v1", "level":N,"prime":p,
                "digits":m,"q_precision_exclusive":NN,
                "short_checkpoint_sha256":self.hashes,
                "saturation_rounds":{str(k):v for k,v in self.rounds.items()},
                "initial_work_digits":m+self.guard,
                "supplier_source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}

    @staticmethod
    def series_parent(sa,digits,NN):
        return sa.PowerSeriesRing(sa.Zmod(5**digits),"q",default_prec=NN)

    def overlap(self,series,weight,key,digits,NN):
        record = self.records[weight]
        expected = record[key]
        if len(series) != len(expected):
            raise ArithmeticError("Wrong replayed basis dimension")
        stop = min(NN,int(record["q_precision_exclusive"]))
        modulus = 5**digits
        for i,f in enumerate(series):
            for n in range(stop):
                if int(f[n]) != int(expected[i][n]) % modulus:
                    raise ArithmeticError(f"M{weight} {key} overlap failed at row{i}, q^{n}")
        return len(series)*stop

    def verify_unit_minor(self,sa,series,weight,NN):
        columns = self.records[weight]["pivot_columns"]
        if max(columns) >= NN:
            raise ArithmeticError("Requested q-depth is too small for the saved unit minor")
        minor = sa.matrix(sa.GF(5),[[f[j] for j in columns] for f in series])
        if minor.nrows() != minor.ncols() or minor.det() == 0:
            raise ArithmeticError("Replayed basis lost its certified mod5 unit minor")

    def replay_saturation(self,sa,series,weight,digits,NN):
        for round_number,operation in enumerate(self.records[weight]["saturation_at_5_operations"],1):
            if operation["divisor"] != 5 or digits <= 1:
                raise ArithmeticError("Invalid saturation divisor or insufficient guard")
            pivots = list(operation["replace_rows"])
            rows = operation["combination_rows"]
            if len(pivots) != len(set(pivots)) or len(rows) != len(pivots):
                raise ArithmeticError("Malformed saturation pivot data")
            parent = series[0].parent()
            next_parent = self.series_parent(sa,digits-1,NN)
            replacements = {}
            for pivot,coefficients in zip(pivots,rows):
                if len(coefficients) != len(series) or coefficients[pivot] != 1:
                    raise ArithmeticError("Malformed saturation kernel row")
                if any(coefficients[j] != int(j == pivot) for j in pivots):
                    raise ArithmeticError("Saturation kernel pivot minor is not the identity")
                combined = parent(0).add_bigoh(NN)
                for coefficient,f in zip(coefficients,series):
                    if coefficient:
                        combined += int(coefficient)*f
                values = [int(combined[n]) for n in range(NN)]
                if any(value % 5 for value in values):
                    raise ArithmeticError("Long saturation combination is not divisible by5")
                replacements[pivot] = next_parent([value//5 for value in values]).add_bigoh(NN)
            series = [replacements.get(i) if i in replacements else
                      f.change_ring(next_parent.base_ring())
                      for i,f in enumerate(series)]
            digits -= 1
            self.emit("long_saturation_round",weight=weight,round=round_number,
                      replaced_rows=len(pivots),remaining_digits=digits)
        checked = self.overlap(series,weight,"q_basis",digits,NN)
        self.verify_unit_minor(sa,series,weight,NN)
        self.emit("long_weight_replay_verified",weight=weight,remaining_digits=digits,
                  short_overlap_coefficients=checked,dimension=len(series))
        return series,digits

    def extend_weight_two(self,sa,spec):
        NN = spec["q_precision_exclusive"]
        digits = spec["initial_work_digits"]
        parent = self.series_parent(sa,digits,NN)
        path = self.output_dir/"M2-long-raw.json.gz"
        report_path = self.output_dir/"M2-long-raw-result.json"
        if self.use_cache and path.exists() and report_path.exists():
            cache_report = read_json(report_path)
            if cache_report.get("request") == spec and cache_report.get("sha256") == raw_json_sha(path):
                cached = read_json(path)
                series = [parent(row).add_bigoh(NN) for row in cached["raw_basis_mod_5work"]]
                self.overlap(series,2,"raw_integer_q_basis",digits,NN)
                self.emit("reused_long_M2_checkpoint",work_digits=digits,q_precision_exclusive=NN)
                return series
        record = self.records[2]
        short_precision = int(record["q_precision_exclusive"])
        needed_precision = max(short_precision,NN)
        self.emit("extending_M2_directly",q_precision_exclusive=needed_precision,
                  work_digits=digits,dimension=record["dimension"])
        started = time.monotonic()
        source = list(sa.ModularForms(self.level,2).q_expansion_basis(prec=needed_precision))
        if len(source) != record["dimension"]:
            raise ArithmeticError("Unexpected dimension of extended M2")
        # The direct Sage basis can change with the requested precision.
        # Recover its exact short coordinate transformation, rather than assuming
        # row indices or normalizations remained unchanged.
        short_source = sa.matrix(sa.QQ,[[f[n] for n in range(short_precision)] for f in source])
        target = sa.matrix(sa.QQ,[[sa.QQ(x) for x in row]
                                  for row in record["raw_integer_q_basis"]])
        pivots = list(short_source.pivots())
        if len(pivots) != record["dimension"]:
            raise ArithmeticError("Extended M2 basis is dependent at short precision")
        change = short_source.matrix_from_columns(pivots).solve_left(
            target.matrix_from_columns(pivots))
        if change*short_source != target:
            raise ArithmeticError("M2 normalization change does not match the short checkpoint")
        series = []
        for coordinate_row in change.rows():
            exact = source[0]*0
            for index in coordinate_row.nonzero_positions():
                exact += coordinate_row[index]*source[index]
            # Global integrality follows from the short full-Sturm certificate;
            # nevertheless every newly produced rational coefficient is checked.
            values = []
            for n in range(NN):
                value = sa.QQ(exact[n])
                if value.denominator() != 1:
                    raise ArithmeticError("Extended raw M2 has an unexpected rational denominator")
                values.append(int(value) % (5**digits))
            series.append(parent(values).add_bigoh(NN))
        checked = self.overlap(series,2,"raw_integer_q_basis",digits,NN)
        capsule = {"request":spec,
                   "M2_short_coordinate_change":[[str(x) for x in row] for row in change.rows()],
                   "raw_basis_mod_5work":[[int(f[n]) for n in range(NN)] for f in series],
                   "short_overlap_coefficients":checked}
        checksum = write_json(path,capsule)
        write_json(report_path,{"request":spec,"sha256":checksum,
                                "elapsed_seconds":time.monotonic()-started})
        self.emit("long_M2_checkpointed",q_precision_exclusive=NN,work_digits=digits,
                  short_overlap_coefficients=checked,sha256=checksum,
                  M2_extension_seconds=time.monotonic()-started)
        return series

    def replay_raw_weight(self,sa,weight,available,digits,NN):
        record = self.records[weight]
        provenance = record["provenance"]
        if provenance["construction"] != "low_weight_products":
            raise ArithmeticError("Long replay requires product/Serre provenance for M4 and M6")
        parent = self.series_parent(sa,digits,NN)
        base_ring = parent.base_ring()
        local = {k:[f.change_ring(base_ring) for f in values]
                 for k,values in available.items()}
        e2 = None
        series = []
        for item in provenance["selected"]:
            kind = item["kind"]
            if kind == "product":
                a,b = map(int,item["weights"])
                i,j = item["basis_indices"]
                if a+b != weight:
                    raise ArithmeticError("Product provenance has the wrong weight")
                value = local[a][i]*local[b][j]
            elif kind == "Eisenstein_oldform":
                k = int(item["weight"])
                level = int(item["V_level"])
                if k != weight or level not in (1,self.level):
                    raise ArithmeticError("Invalid Eisenstein provenance")
                scale = sa.QQ(item["scale"])
                multiplier = -scale*sa.QQ(2*k)/sa.bernoulli(k)
                coefficients = [sa.QQ(scale)]+[sa.QQ(0)]*(NN-1)
                for n in range(1,(NN-1)//level+1):
                    coefficients[level*n] = multiplier*sa.sigma(n,k-1)
                if any(x.denominator() != 1 for x in coefficients):
                    raise ArithmeticError("Unexpected nonintegral scaled Eisenstein coefficients")
                value = parent([sa.ZZ(x) for x in coefficients]).add_bigoh(NN)
            elif kind == "scaled_Serre_derivative":
                source_weight = int(item["source_weight"])
                value = local[source_weight][item["source_basis_index"]]
                if e2 is None:
                    e2 = parent([1]+[-24*sa.sigma(n,1) for n in range(1,NN)]).add_bigoh(NN)
                current = source_weight
                for step in item["steps"]:
                    divisor = int(sa.gcd(current,12))
                    if step != {"input_weight":current,"theta_multiplier":12//divisor,
                                "E2_multiplier":current//divisor}:
                        raise ArithmeticError("Invalid scaled Serre derivative provenance")
                    value = step["theta_multiplier"]*parent.gen()*value.derivative()-step["E2_multiplier"]*e2*value
                    current += 2
                if current != weight:
                    raise ArithmeticError("Serre derivative reaches the wrong weight")
            else:
                raise ArithmeticError("Unsupported low-weight provenance: "+str(kind))
            series.append(value)
        checked = self.overlap(series,weight,"raw_integer_q_basis",digits,NN)
        self.emit("long_raw_weight_replayed",weight=weight,work_digits=digits,
                  short_overlap_coefficients=checked,dimension=len(series))
        return series

    def __call__(self,N,p,m,NN):
        import sage.all as sa
        spec = self.specification(N,p,m,NN)
        m,NN = int(m),int(NN)
        self.emit("low_weight_supplier_started",request=spec)
        final_path = self.output_dir/"low-weight-bases.json.gz"
        report_path = self.output_dir/"supplier-result.json"
        if self.use_cache and final_path.exists() and report_path.exists():
            report = read_json(report_path)
            if report.get("request") == spec and report.get("uncompressed_capsule_sha256") == raw_json_sha(final_path):
                cached = read_json(final_path)
                parent = self.series_parent(sa,m,NN)
                result = [[parent(row).add_bigoh(NN) for row in cached["bases"][str(k)]]
                          for k in WEIGHTS]
                for k,basis in zip(WEIGHTS,result):
                    self.overlap(basis,k,"q_basis",m,NN)
                    self.verify_unit_minor(sa,basis,k,NN)
                self.emit("reused_complete_long_basis_package",q_precision_exclusive=NN,digits=m)
                return result,6
        available = {}
        current_digits = spec["initial_work_digits"]
        raw2 = self.extend_weight_two(sa,spec)
        available[2],current_digits = self.replay_saturation(sa,raw2,2,current_digits,NN)
        for weight in (4,6):
            raw = self.replay_raw_weight(sa,weight,available,current_digits,NN)
            available[weight],current_digits = self.replay_saturation(sa,raw,weight,current_digits,NN)
            checksum = write_json(self.output_dir/f"M{weight}-long-basis.json.gz",
                                 {"request":spec,"weight":weight,"remaining_digits":current_digits,
                                  "basis":[[int(f[n]) for n in range(NN)] for f in available[weight]]})
            self.emit("long_weight_checkpointed",weight=weight,remaining_digits=current_digits,sha256=checksum)
        if current_digits != m:
            raise ArithmeticError("Saturation guard accounting did not reach the requested precision")
        final_ring = sa.Zmod(5**m)
        result = [[f.change_ring(final_ring) for f in available[k]] for k in WEIGHTS]
        capsule = {"schema":"certified-low-weight-replay-v1", "request":spec,"weight_bound":6,
                   "bases":{str(k):[[int(f[n]) for n in range(NN)] for f in basis]
                            for k,basis in zip(WEIGHTS,result)},
                   "scope":"Exact modular replay of proven finite low-weight bases. Higher-weight generation is checked by Sage's complementary-space ranks; no global generator conjecture is assumed."}
        checksum = write_json(final_path,capsule)
        report = {"status":"low_weight_replay_passed","request":spec,
                  "dimensions":{str(k):len(basis) for k,basis in zip(WEIGHTS,result)},
                  "weight_bound":6,"uncompressed_capsule_sha256":checksum,
                  "elapsed_seconds":time.monotonic()-self.started,
                  "long_QQ_rank_computed":False,"direct_weights_extended":[2],
                  "all_short_overlaps_checked":True,"all_long_divisions_by_5_checked":True,
                  "scope":capsule["scope"]}
        write_json(report_path,report)
        self.emit("low_weight_supplier_passed",dimensions=report["dimensions"],
                  q_precision_exclusive=NN,digits=m,sha256=checksum)
        return result,6


@contextmanager
def installed_supplier(hs, checkpoint_dir, output_dir, progress=None, **kwargs):
    """Temporarily replace only hs.low_weight_generators; restore on every exit."""
    original = hs.low_weight_generators
    supplier = SavedBasisSupplier(checkpoint_dir,output_dir,progress=progress,**kwargs)
    hs.low_weight_generators = supplier
    try:
        yield supplier
    finally:
        hs.low_weight_generators = original


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkpoints",type=Path,required=True)
    parser.add_argument("--output",type=Path,default=Path("katz-low-weight-replay"))
    parser.add_argument("--digits",type=int,default=8)
    parser.add_argument("--q-precision",type=int,default=6830)
    parser.add_argument("--maximum-guard",type=int,default=30)
    parser.add_argument("--no-cache",action="store_true")
    parser.add_argument("--plan",action="store_true")
    args = parser.parse_args()
    supplier = SavedBasisSupplier(args.checkpoints,args.output,
                                  maximum_guard=args.maximum_guard,use_cache=not args.no_cache)
    if args.plan:
        print(json.dumps(supplier.specification(supplier.level,5,args.digits,args.q_precision),indent=2))
    else:
        supplier(supplier.level,5,args.digits,args.q_precision)


if __name__ == "__main__":
    main()
