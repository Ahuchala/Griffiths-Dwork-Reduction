-- CayleyGriffithsRingCI.m2
--
-- Griffiths ring for a smooth complete intersection Z = Z_{d_1,...,d_c} in
-- Gr(k, n), via the Cayley trick (Fatighenti-Mongardi, "A note on a
-- Griffiths-type ring for complete intersections in Grassmannians",
-- Theorem 4.x; thesis Chapter 4).
--
-- Construction.  Let Y = P(E), E = (+) O_G(d_i), and Yhat the Cayley
-- hypersurface.  In the Cox ring S[y_1,...,y_c] of P(E) with bigrading
--     deg x_I = (0,1),   deg y_i = (1, -d_i),
-- set F = sum_i y_i f_i (the f_i cut out Z).  The Griffiths ring is
--     U = S[y]/( F, f_1,...,f_c, { D_{x_I} F } ),
-- where D_{x_I} are the sl_n derivations D^i_j = sum_l x_{l,i} d/dx_{l,j}.
--
-- IMPORTANT.  U is NOT Artinian (Krull dim > 0) and is not meant to be:
-- one reads a single bigraded slice.  With m := (sum d_i) - n the adjunction
-- degree (omega_Z = O_Z(m)), the Hodge data sits in the column b = m:
--     U_{p, m} = H^{N-c-p, p}_van(Z)            (dim Z even)
--     U_{p, m} = H^{N-c-p, p}_van(Z) (+) delta_{p,(N-c)/2} I_{p,p-1}(G)   (dim Z odd)
-- where N = k(n-k) and I_{p,p-1}(G) is the primitive-ambient correction
-- (cokernel of cup-with-hyperplane on H^{p-1,p-1}(G) -> H^{p,p}(G)).
--
-- Do NOT saturate by the irrelevant ideal; that destroys the slice.
--
-- Default: Z_{2,1} in Gr(2,5) (Gushel-Mukai fourfold), which has a nonzero
-- ambient correction V_5 in U_{2,-2}.  Edit (k, n, degs) for other cases.
--
-- Run with:  M2 --script CayleyGriffithsRingCI.m2

needsPackage "Resultants";
needsPackage "TensorComplexes";  -- multiSubsets
needsPackage "Schubert2";        -- independent Hodge-number check

allowableThreads = 8;

-- ===================== parameters =====================
k    = 2;
n    = 7;
degs = {1,1,1, 1,1,1,1};          -- multidegrees d_i (any order)
K    = ZZ/101;          -- finite field for speed; QQ for exact

c = #degs;
N = k*(n-k);
m = (sum degs) - n;     -- adjunction degree; omega_Z = O_Z(m)
dimZ = N - c;

-- ===================== Plucker ring of Gr(k,n) =====================
pluckerIdeal = Grassmannian(k-1, n-1, CoefficientRing => K);
R = ring pluckerIdeal;
gensR = gens R;
numGens = #gensR;

countInversions = (perm) -> (
    ans := 0;
    for i from 0 to #perm-2 do for j from i+1 to #perm-1 do
        if perm#j < perm#i then ans = ans + 1;
    ans);

hasDuplicates = (ls) -> (unique ls != ls);

-- antisymmetrize: define p_(perm) for all index orders
for inds in multiSubsets(n,k) do (
    if hasDuplicates(inds) then (
        for perm in permutations(inds) do p_(toSequence perm) = 0;
    ) else for perm in permutations(inds) do
        p_(toSequence perm) = (-1)^(countInversions perm) * p_(toSequence inds);
);

getIndex = (mon) -> (baseName mon)#1;
exponentToMonomial = (ls) -> product(for i from 0 to numGens-1 list (gensR#i)^(ls#i));

-- sl_n derivation D^i_j applied to a single power p_I^e
differentiateMonomial = (i,j,mon) -> (
    monIdx := (exponents mon)#0;
    e := sum monIdx;
    ind := position((exponents mon)#0, lam -> lam == e);
    monomial := gensR#ind;
    ls := getIndex monomial;
    if not member(j, ls) then return 0;
    if (i != j) and member(i, ls) then return 0;
    e * p_(replace(position(ls, lam -> lam == j), i, ls)) * p_ls^(e-1));

-- D^i_j on an arbitrary polynomial (product rule over Plucker monomials)
differentiatePolynomial = (i,j,poly) -> (
    ans := 0;
    for monomial in terms poly do (
        el := ((listForm monomial)#0)#0;
        co := ((listForm monomial)#0)#1;
        for li from 0 to numGens-1 do if el#li > 0 then (
            mon := (gensR#li)^(el#li);
            mOver := new MutableList from el; mOver#li = 0;
            mOver = exponentToMonomial(toList mOver);
            ans = ans + co * differentiateMonomial(i,j,mon) * mOver;
        );
    );
    ans);

-- ===================== the complete intersection =====================
-- generic forms f_i of degree d_i.  Re-run if not smooth (check below / companion).
randForm = (d) -> sum(flatten entries basis(d, R), mon -> random(1,99) * mon);
flist = for d in degs list randForm d;

-- ===================== Cayley ring =====================
-- precompute the sl_n action on each f_i (in the Plucker ring, where the
-- differentiator is validated)
Ef = for l from 0 to c-1 list (
    for a from 0 to n-1 list for b from 0 to n-1 list differentiatePolynomial(a,b, flist#l));

-- Cox ring with bigrading deg x_I = (0,1), deg y_i = (1, -d_i)
ydegs = for d in degs list {1, -d};
S = K[gensR, y_0 .. y_(c-1), Degrees => (for v in gensR list {0,1}) | ydegs];
phi = map(S, R, (gens S)_{0..numGens-1});
yv = for i from 0 to c-1 list S_(numGens + i);

F = sum(c, l -> yv#l * phi(flist#l));

-- generators of the ideal:
--   F, the f_i (= dF/dy_i), and the sl_n action D_{x_I}F = sum_l y_l (E_{ab} f_l)
offdiag = flatten for a from 0 to n-1 list for b from 0 to n-1 list (
    if a == b then continue;
    sum(c, l -> yv#l * phi(Ef#l#a#b)));
diagdiff = for a from 0 to n-2 list
    sum(c, l -> yv#l * phi(Ef#l#a#a - Ef#l#(a+1)#(a+1)));
ypart = for l from 0 to c-1 list phi(flist#l);

J = ideal(select(offdiag | diagdiff | ypart | {F}, z -> z != 0)) + phi(pluckerIdeal);
U = S/J;

-- ===================== read the Hodge slice b = m =====================
print("Z = CI" | toString degs | " in Gr(" | toString k | "," | toString n | ")"
    | "  dim Z = " | toString dimZ | ",  m = " | toString m);
print "";
print("Griffiths ring slice U_{p, m} (p = 0..dim Z), m = " | toString m | ":");
slice = for p from 0 to dimZ list hilbertFunction({p, m}, U);
print toString slice;
print("These are H^{" | toString(dimZ) | "-p, p}_van(Z)"
    | (if odd dimZ then ", with the ambient correction I_{p,p-1}(G) added at p = (dim Z)/2." else "."));

-- ===================== independent Schubert2 check =====================
print "";
print "Schubert2 cross-check (vanishing Hodge-Euler of Z):";
G = flagBundle {k, n-k};
Ebund = OO_G(degs#0);
for i from 1 to c-1 do Ebund = Ebund ++ OO_G(degs#i);
Zs = sectionZeroLocus Ebund;
OmZ = cotangentBundle Zs;
OmG = cotangentBundle G;
chiZ = for j from 0 to dimZ list chi exteriorPower(j, OmZ);
print("  chi(Omega^j_Z), j=0..dimZ: " | toString chiZ);
print("  chi_top(Z) = " | toString sum(for j from 0 to dimZ list (-1)^j * chiZ#j));
-- primitive-ambient correction I_{p,p-1}(G): cokernel of cup-with-O(1) on H^{*,*}(G)
hGr = (j) -> #select(flatten entries basis(j, R), mn -> true) - (if j>=1 then #select(flatten entries basis(j-1,R), mn->true) else 0);
print "";
print("If dim Z is odd, the correction I at p = (dim Z)/2 is the primitive ambient class");
print("(e.g. V_5 for Gr(2,5)); compare the middle entry of the slice above against");
print("H^{(dimZ)/2,(dimZ)/2}_van(Z) to isolate it.");
