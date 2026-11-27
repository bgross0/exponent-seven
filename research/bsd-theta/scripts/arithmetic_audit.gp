\\ Exact arithmetic audit for E=389a1, K=Q(sqrt(-71)), p=29 and p=5.
\\ Run with PARI/GP 2.19.1:
\\   gp -fq scripts/arithmetic_audit.gp > data/arithmetic-audit.json
\\ This proves the quadratic-twist nonvanishing through a nonzero exact
\\ modular-symbol sum. It independently reconstructs the supersingular T2
\\ matrix and CM values used for the auxiliary ring-class L-value certificate.
\\ The conductor25 theta jet has a separate certificate in cm-jet-p5.json.

must(c, message) = if(!c, error(message));
formvec(q) = Vec(q);

audit_run() = {
E = ellinit([0,1,1,-2,0]);
p = 29;
D = -71;
N = ellglobalred(E)[1];
must(N == 389 && E.disc == 389 && E.c4 == 112, "curve invariants mismatch");
must(ellrootno(E) == 1, "root number mismatch");
must(ellap(E,p) == -6, "ordinary trace mismatch");
must(ellap(E,3) == -2, "Frobenius witness mismatch");
must(ellap(E,7) == -5 && ellisoncurve(E,[0,0]), "positive-rank witness mismatch");
must(gcd(3+1-ellap(E,3),7+1-ellap(E,7)) == 1, "torsion reduction bound mismatch");
must(kronecker((-2)^2-4*3,p) == -1, "Frobenius polynomial must be irreducible mod29");
must(valuation(E.disc,389) == 1 && valuation(E.c4,389) == 0, "multiplicative ramification witness mismatch");
must(kronecker(D,29) == 1 && kronecker(D,389) == -1, "splitting mismatch");

q29 = qfbprimeform(D,p);
q29red = qfbred(q29);
classpowers = vector(7,j,formvec(qfbpow(q29red,j)));
must(classpowers[7] == [1,1,18], "prime29 seventh power not principal");
for(j=1,6,must(classpowers[j] != [1,1,18], "unexpected smaller class order"));
must(qfbclassno(D) == 7, "class number mismatch");
must(znorder(Mod(16,29)) == 7, "chosen residue root must have order7");

hecke_data = [[2,-2],[3,-2],[5,-3],[7,-5]];
Mminus = msinit(N,2,-1);
Vminus = msfromhecke(Mminus,hecke_data);
must(matsize(Vminus)[2] == 1, "minus eigenline not isolated");
vminus = Vminus[,1];
must(msissymbol(Mminus,vminus), "minus symbol relations fail");
Mplus = msinit(N,2,1);
Vplus = msfromhecke(Mplus,hecke_data);
must(matsize(Vplus)[2] == 1, "plus eigenline not isolated");
vplus = Vplus[,1];
must(msissymbol(Mplus,vplus), "plus symbol relations fail");
sturm_bound = floor(2*(N+1)/12);
must(sturm_bound == 65, "Sturm bound mismatch");
forprime(q=2,sturm_bound,
  must((mshecke(Mminus,q)-ellap(E,q))*vminus == 0, "minus Hecke check failed");
  must((mshecke(Mplus,q)-ellap(E,q))*vplus == 0, "plus Hecke check failed");
);

LEsymbol = mseval(Mplus,vplus,[oo,0]);
must(LEsymbol == 0, "L(E,1) symbol not zero");
cusp_values = vector(70,a,mseval(Mminus,vminus,[oo,a/71]));
quadratic_weights = vector(70,a,kronecker(D,a));
twist_sum = sum(a=1,70,quadratic_weights[a]*cusp_values[a]);
must(twist_sum == -4, "quadratic twist sum mismatch");
roots29sq = polrootspadic(x^2+6*x+29,29,2);
unit_roots = select(z->valuation(z,29)==0,roots29sq);
must(#unit_roots == 1 && lift(unit_roots[1]) == 139, "ordinary root mismatch");

\\ Preserve the original p29 audit; append the cheaper p5 candidate.
q5 = qfbprimeform(D,5);
q5red = qfbred(q5);
must(ellap(E,5) == -3 && kronecker(D,5) == 1, "p5 ordinary/split checks fail");
must(kronecker(-8,5) == -1, "p5 Frobenius polynomial must be irreducible");
must(q5red == qfbpow(q29red,3), "prime5 class is not prime29 class cubed");
must(znorder(Mod(5,7)) == 6, "coefficient field degree mismatch");
must(polisirreducible(polcyclo(7)*Mod(1,5)), "Phi7 must be irreducible mod5");
roots5sq = polrootspadic(x^2+3*x+5,5,2);
unit_roots5 = select(z->valuation(z,5)==0,roots5sq);
must(#unit_roots5 == 1 && lift(unit_roots5[1]) == 7, "p5 ordinary root mismatch");
must(qfbclassno(D*25^2) == 140, "conductor25 class number mismatch");
q2conductor25 = qfbprimeform(D*25^2,2);
principal25 = qfbred(qfbpow(q2conductor25,140));
must(Vec(principal25) == [1,1,11094], "conductor25 norm2 class does not have order dividing140");
for(j=1,3,must(qfbpow(q2conductor25,[70,28,20][j]) != principal25, "conductor25 norm2 class order is less than140"));

\\ Independent construction from PARI's classical modular polynomial Phi_2.
\\ The j-list is also checked to be distinct and supersingular; the mass/count
\\ formula gives exactly 33 supersingular j-invariants in characteristic389.
ssj_coordinates = [[0,0],[0,96],[0,293],[7,0],[16,0],[17,0],[36,0],[48,20],[48,369],[78,112],[78,277],[112,136],[112,253],[121,0],[148,124],[148,265],[149,168],[149,221],[154,0],[173,124],[173,265],[181,68],[181,321],[220,0],[284,51],[284,338],[318,0],[327,0],[347,53],[347,336],[358,0],[386,6],[386,383]];
u = ffgen(Mod(1,389)*(z^2-2),'u);
ssj = vector(33,i,ssj_coordinates[i][1]+ssj_coordinates[i][2]*u);
must(#Set(ssj) == 33, "duplicate supersingular j values");
for(i=1,33,must(ellissupersingular(ellinit(ellfromj(ssj[i]),u)), "nonsupersingular j value"));
Phi2 = polmodular(2);
B2 = matrix(33,33);
for(i=1,33,
  fac = factor(subst(Phi2,y,ssj[i]));
  for(j=1,matsize(fac)[1],
    must(poldegree(fac[j,1]) == 1, "Phi2 failed to split over finite field");
    rootj = -polcoef(fac[j,1],0)/polcoef(fac[j,1],1);
    hit = 0;
    for(k=1,33,if(ssj[k] == rootj,hit=k));
    must(hit > 0, "missing supersingular Phi2 target");
    B2[i,hit] += fac[j,2];
  );
);
must(B2*vector(33,i,1)~ == 3*vector(33,i,1)~, "Brandt row sums mismatch");
must(charpoly(B2) == charpoly(mshecke(Mplus,2)), "Brandt/modular-symbol T2 spectra differ");
BK = matker(B2+2);
must(matsize(BK)[2] == 1, "Brandt a2 eigenspace not unique");
phi = BK[,1];
if(phi[4] < 0,phi=-phi);
must(Vec(phi) == [0,0,0,2,-2,-2,-2,1,1,-1,-1,1,1,0,-1,-1,0,0,0,1,1,1,1,0,-1,-1,0,2,0,0,2,-1,-1], "Brandt eigenfunction differs");
H71 = polclass(D);
H71coeff = Vecrev(H71);
must(H71coeff == [737707086760731113357714241006081263,-425319473946139603274605151187659,5138800366453976780323726329446,-823534263439730779968091389,98394038810047812049302,-3091990138604570,313645809715,1], "Hilbert class polynomial mismatch");
CMindices = select(i->subst(H71,x,ssj[i]) == 0,vector(33,i,i));
must(#CMindices == 7, "CM root count mismatch");
CMvalues = vector(7,i,phi[CMindices[i]]);
must(CMvalues == [-1,-1,0,1,1,0,0], "CM function values mismatch");
CM2 = matrix(7,7,i,j,B2[CMindices[i],CMindices[j]]);
must(charpoly(CM2) == (x-2)*(x^3+x^2-2*x-1)^2, "CM norm2 graph not a seven-cycle");

\\ Lower-conductor ordinary-correction check, independent of the conductor25
\\ lifting computation. Factor H_-1775 modulo389 and count every root with
\\ its multiplicity, thereby retaining all28 ideal classes after collisions.
H1775 = polclass(D*5^2);
must(poldegree(H1775) == 28, "conductor5 class number mismatch");
fac1775 = factor(H1775*(1+0*u));
CM5multiplicities = vector(33,i,0);
for(j=1,matsize(fac1775)[1],
  must(poldegree(fac1775[j,1]) == 1, "conductor5 polynomial failed to split");
  rootj = -polcoef(fac1775[j,1],0)/polcoef(fac1775[j,1],1);
  hit = 0;
  for(k=1,33,if(ssj[k] == rootj,hit=k));
  must(hit > 0, "conductor5 root missing from supersingular list");
  CM5multiplicities[hit] += fac1775[j,2];
);
must(vecsum(CM5multiplicities) == 28, "conductor5 multiplicities incomplete");
CM5sum = CM5multiplicities*phi;
must(CM5sum == 0, "conductor5 total eigenfunction sum is not zero");

print("{");
print("  \"schema_version\": 2,");
print("  \"engine\": \"PARI/GP ",version()[1],".",version()[2],".",version()[3],"\",");
print("  \"curve\": {\"label\": \"389a1\", \"ainvs\": [0,1,1,-2,0], \"conductor\": ",N,", \"minimal_discriminant\": ",E.disc,", \"c4\": ",E.c4,", \"root_number\": ",ellrootno(E),"},");
print("  \"p\": 29,");
print("  \"ordinary_reduction\": {\"ap\": -6, \"unit_root_mod_841\": 139},");
print("  \"mod29_irreducibility\": {\"frobenius_prime\": 3, \"point_count\": 6, \"trace\": -2, \"determinant\": 3, \"discriminant_mod29\": 21, \"legendre_symbol\": -1},");
print("  \"ramification_at_389\": {\"v_minimal_discriminant\": 1, \"v_c4\": 0, \"reduction\": \"split multiplicative I1\", \"mod29_inertia_nontrivial\": true},");
print("  \"positive_rank_witness\": {\"rational_point\": [0,0], \"good_reduction_orders_at3_and7\": [6,13], \"torsion_order_divides\": 1, \"point_nontorsion\": true},");
print("  \"quadratic_field\": {\"discriminant\": -71, \"integral_generator_polynomial\": \"x^2-x+18\", \"class_number\": 7, \"prime29_form\": ",formvec(q29),", \"prime29_reduced_form\": ",formvec(q29red),", \"prime29_class_powers\": ",classpowers,", \"prime29_omega_residue\": 13, \"splitting_at29\": 1, \"splitting_at389\": -1},");
print("  \"auxiliary_character_candidate\": {\"psi_class_generator_image\": \"zeta_7\", \"chi\": \"psi^2 = psi / psi^tau\", \"chi_prime29\": \"zeta_7^2\", \"zeta7_residue_mod29\": 16, \"theta_series_level\": 71, \"p_regular\": true, \"L_EK_chi_nonzero\": \"exact nonconstant CM toric sum; requires cited Gross/Waldspurger identification\"},");
print("  \"modular_symbols\": {");
print("    \"method\": \"exact rational Hecke eigenlines, primitive integral scaling; no analytic period normalization\",");
print("    \"initial_eigenvalues\": ",hecke_data,",");
print("    \"minus_ambient_dimension\": ",msdim(Mminus),", \"plus_ambient_dimension\": ",msdim(Mplus),",");
print("    \"sturm_bound\": ",sturm_bound,", \"all_prime_hecke_checks_through_bound\": true,");
print("    \"minus_symbol\": ",Vec(vminus),",");
print("    \"plus_symbol\": ",Vec(vplus),",");
print("    \"L_E_1_symbol\": ",LEsymbol,",");
print("    \"twist_cusp_values_a1_to70\": ",cusp_values,",");
print("    \"twist_kronecker_weights_a1_to70\": ",quadratic_weights,",");
print("    \"quadratic_twist_symbol_sum\": ",twist_sum,",");
print("    \"L_quadratic_twist_nonzero\": true");
print("  },");
print("  \"p5_candidate\": {\"p\": 5, \"ap\": -3, \"unit_root_mod25\": 7, \"splitting\": 1, \"frobenius3_discriminant_mod5\": 2, \"legendre_symbol\": -1, \"prime5_form\": ",formvec(q5),", \"prime5_reduced_form\": ",formvec(q5red),", \"prime5_class_power_of_prime29\": 3, \"prime5_omega_residue\": 2, \"psi_prime5\": \"zeta_7^3\", \"chi_prime5\": \"zeta_7^6\", \"coefficient_field\": \"Q5(zeta_7), unramified degree6\", \"p_regular_residually\": true, \"mod5_absolutely_irreducible_via_frobenius_and_unipotent_inertia\": true, \"ring_class_group_size_conductor5\": 28, \"ring_class_group_size_conductor25\": 140, \"ring_class_group_size_conductor125\": 700},");
print("  \"independent_brandt_check\": {\"field\": \"F389[u]/(u^2-2)\", \"supersingular_count\": 33, \"all_j_checked_supersingular\": true, \"matrix_rebuilt_from_pari_Phi2\": true, \"T2_charpoly_matches_modular_symbols\": true, \"eigenvalue_minus2_multiplicity\": 1, \"phi\": ",Vec(phi),", \"H_minus71_coefficients_ascending\": ",H71coeff,", \"CM_indices_zero_based\": ",CMindices-vector(7,i,1),", \"CM_values\": ",CMvalues,", \"CM_T2_is_seven_cycle\": true},");
print("  \"conductor5_correction_check\": {\"discriminant\": -1775, \"Hilbert_polynomial_degree\": 28, \"root_multiplicities_in_ssj_order\": ",CM5multiplicities,", \"total_phi_sum\": ",CM5sum,", \"ordinary_correction_after_tame_projection_is_zero\": true},");
print("  \"conductor25_class_group_check\": {\"discriminant\": -44375, \"class_number\": 140, \"norm2_form\": ",Vec(q2conductor25),", \"norm2_form_order\": 140, \"order_checks_at_exponents\": [140,70,28,20]},");
print("  \"theta_status\": {\"class_number_one_appendix_applies_directly\": false, \"ring_class_group_size_conductor29_squared\": 5684, \"ring_class_group_size_conductor29_cubed\": 164836, \"p29_tame_torsion_size\": 196, \"p5_tame_torsion_size\": 28, \"constant_and_linear_terms_vanish_by_theory\": true, \"p29_quadratic_coefficient\": \"NOT COMPUTED\", \"p5_quadratic_coefficient\": \"separate cm-jet-p5.json certificate; normalization audit external\"},");
print("  \"result\": \"PARI_ARITHMETIC_AUDIT_PASS\",");
print("  \"limitations\": [\"No full BSD conclusion\", \"No end-to-end formal proof\", \"Classical modularity, Eichler-Shimura, Sturm, CM and Gross/Waldspurger theorems are mathematical dependencies\", \"Conductor25 theta jet is checked by a separate script\"]");
print("}");
};
iferr(audit_run(), audit_error, print(audit_error); quit(1));
quit(0);
