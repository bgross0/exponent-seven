#!/usr/bin/env python3
"""Weight-two Manin-symbol computation at prime level, over Q or Z/(5^d).

The module is relative modular symbols, before removing the boundary.
All matrices use columns for images.  Continued fractions implement Hecke
actions; T2 also has an independent four-matrix Manin implementation.
"""
from fractions import Fraction
from math import gcd, isqrt


def normalize(value, modulus):
    return value % modulus if modulus else Fraction(value)


def add_sparse(row, column, value, modulus):
    value = normalize(row.get(column, 0)+value, modulus)
    if value:
        row[column] = value
    else:
        row.pop(column, None)


def rref_mod(rows, ncols, modulus):
    """RREF over a prime-power ring, requiring every chosen pivot a unit."""
    rows = [[v % modulus for v in row] for row in rows]
    pivots, i = [], 0
    for j in range(ncols):
        k = next((k for k in range(i, len(rows)) if gcd(rows[k][j], modulus) == 1), None)
        if k is None:
            if any(rows[k][j] for k in range(i, len(rows))):
                raise ValueError(f"Nonunit pivot column {j}; a Smith computation is needed")
            continue
        rows[i], rows[k] = rows[k], rows[i]
        inv = pow(rows[i][j], -1, modulus)
        rows[i] = [x*inv % modulus for x in rows[i]]
        for k, row in enumerate(rows):
            if k != i and row[j]:
                coefficient = row[j]
                rows[k] = [(a-coefficient*b) % modulus for a,b in zip(row, rows[i])]
        pivots.append(j)
        i += 1
        if i == len(rows):
            break
    return rows, pivots


def kernel_mod(rows, ncols, modulus):
    a, pivots = rref_mod(rows, ncols, modulus)
    basis = []
    for j in range(ncols):
        if j in pivots:
            continue
        col = [0]*ncols
        col[j] = 1
        for i, p in enumerate(pivots):
            col[p] = -a[i][j] % modulus
        basis.append(col)
    return basis


def matmul(A, B, modulus):
    cols = list(zip(*B))
    return [[normalize(sum(x*y for x,y in zip(row,col)),modulus) for col in cols] for row in A]


class PrimeManin:
    def __init__(self, level, digits=1, exact=False):
        assert level > 3 and all(level % d for d in range(2, isqrt(level)+1))
        self.level, self.modulus = level, 0 if exact else 5**digits
        self.relations = []
        for i in range(level+1):
            c,d = self.pair(i)
            row = {}
            for j in (i, self.index(d,-c)):
                add_sparse(row,j,1,self.modulus)
            self.relations.append(row)
            row = {}
            for j in (i, self.index(d,-c-d), self.index(-c-d,c)):
                add_sparse(row,j,1,self.modulus)
            self.relations.append(row)
        # Sparse forward elimination. In these prime-level examples the
        # pivots are units, which is verified rather than assumed.
        pivots = {}
        for relation in self.relations:
            row = dict(relation)
            while row:
                j = min(row)
                if j not in pivots:
                    inv = pow(row[j], -1, self.modulus) if self.modulus else 1/row[j]
                    pivots[j] = {k:normalize(v*inv,self.modulus) for k,v in row.items()}
                    break
                factor = row[j]
                for k,v in pivots[j].items():
                    add_sparse(row,k,-factor*v,self.modulus)
        self.free = [i for i in range(level+1) if i not in pivots]
        self.dimension = len(self.free)
        free_index = {j:i for i,j in enumerate(self.free)}
        self.reduction = {}
        for j in range(level, -1, -1):
            if j in free_index:
                self.reduction[j] = {free_index[j]:1}
            else:
                row = {}
                for k,v in pivots[j].items():
                    if k == j:
                        continue
                    for q,w in self.reduction[k].items():
                        add_sparse(row,q,-v*w,self.modulus)
                self.reduction[j] = row
        assert all(not self.reduce(r) for r in self.relations)

    def pair(self, i):
        return (0,1) if i == self.level else (1,i)

    def index(self, c, d):
        c,d = c % self.level,d % self.level
        assert c or d
        return d*pow(c,-1,self.level) % self.level if c else self.level

    def reduce(self, symbol):
        row = {}
        for j,v in symbol.items():
            for k,w in self.reduction[j].items():
                add_sparse(row,k,v*w,self.modulus)
        return row

    def lift_endpoints(self, i):
        # SL2 lift [[0,-1],[1,i]], or I for (0:1).
        if i == self.level:
            return Fraction(0), None
        return (Fraction(-1,i) if i else None), Fraction(0)

    def infinity_path(self, r):
        """Manin expression for {infinity,r}; None denotes infinity."""
        if r is None:
            return {}
        a,b = r.numerator,r.denominator
        p0,q0,p1,q1 = 0,1,1,0
        out = {}
        while b:
            c = a//b
            p2,q2 = c*p1+p0,c*q1+q0
            determinant = p2*q1-p1*q2
            assert abs(determinant) == 1
            # Columns are endpoint and startpoint, with sign adjusted for det1.
            index = self.index(determinant*q2, q1)
            add_sparse(out,index,1,self.modulus)
            p0,q0,p1,q1 = p1,q1,p2,q2
            a,b = b,a-c*b
        return out

    def path(self, start, end):
        out = self.infinity_path(end)
        for j,v in self.infinity_path(start).items():
            add_sparse(out,j,-v,self.modulus)
        return out

    def hecke_symbol(self, i, ell):
        assert self.level % ell
        start,end = self.lift_endpoints(i)
        out = {}
        for r in range(ell+1):
            def action(z):
                if z is None:
                    return None
                return ell*z if r == ell else (z+r)/ell
            for j,v in self.path(action(start),action(end)).items():
                add_sparse(out,j,v,self.modulus)
        return self.reduce(out)

    def hecke(self, ell, check_relations=True):
        images = [self.hecke_symbol(i,ell) for i in range(self.level+1)]
        if check_relations:
            for relation in self.relations:
                out = {}
                for i,c in relation.items():
                    for j,v in images[i].items():
                        add_sparse(out,j,c*v,self.modulus)
                assert not out, ("Hecke failed Manin relation",ell,relation,out)
        return [[images[i].get(j,0) for i in self.free] for j in range(self.dimension)]

    def hecke_two_merel(self):
        matrices = [(1,0,0,2),(2,0,0,1),(2,1,0,1),(1,0,1,2)]
        images = []
        for i in self.free:
            c,d = self.pair(i)
            row = {}
            for a,b,x,y in matrices:
                add_sparse(row,self.index(c*a+d*x,c*b+d*y),1,self.modulus)
            images.append(self.reduce(row))
        return [[images[i].get(j,0) for i in range(self.dimension)] for j in range(self.dimension)]

    def boundary_row(self):
        # At prime level a cusp is equivalent to infinity iff its reduced
        # denominator is divisible by the level; all other cusps are 0.
        def cusp(r):
            return int(r is None or r.denominator % self.level == 0)
        row = []
        for i in self.free:
            a,b = self.lift_endpoints(i)
            row.append(normalize(cusp(b)-cusp(a),self.modulus))
        return row

    def conjugation(self):
        # z -> -conjugate(z) fixes infinity and negates real cusps.
        images = []
        for i in self.free:
            a,b = self.lift_endpoints(i)
            a = -a if a is not None else None
            b = -b if b is not None else None
            images.append(self.reduce(self.path(a,b)))
        return [[images[i].get(j,0) for i in range(self.dimension)] for j in range(self.dimension)]
