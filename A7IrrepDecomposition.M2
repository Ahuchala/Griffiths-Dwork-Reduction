needsPackage "TensorComplexes";
needsPackage "Cyclotomic";

allowableThreads = 8;
n = 10;
k = 3;

K = toField(QQ[t]/(t^2 + t + 2))
vv = K_0        -- satisfies vv^2 + vv + 2 = 0
ww = -1 - vv
-- no z, zeta3, zeta7 needed anymore since ls1, ls2 are integer lists

pluckerIdeal = Grassmannian(k-1, n-1, CoefficientRing => K);
R = ring pluckerIdeal;
gensR   = gens R;
numGens = #gensR;

countInversions = (perm) -> (
    ans := 0;
    for i from 0 to #perm-2 do
        for j from i+1 to #perm-1 do
            if perm#j < perm#i then ans = ans + 1;
    ans
);

hasDuplicates = (myls) -> unique myls != myls;

for inds in multiSubsets(n, k) do (
    if hasDuplicates inds then (
        for perm in permutations inds do p_(toSequence perm) = 0;
    ) else (
        for perm in permutations inds do
            p_(toSequence perm) = (-1)^(countInversions perm) * p_(toSequence inds);
    );
);

getIndex = (mon) -> (baseName mon)#1;

exponentToMonomial = (expList) ->
    product(for i from 0 to numGens-1 list gensR#i ^ (expList#i));

differentiateMonomial = (i, j, mon) -> (
    monomialIndex := (exponents mon)#0;
    exponent      := sum monomialIndex;
    ind           := position(monomialIndex, e -> e == exponent);
    monomial      := gensR#ind;
    idx           := getIndex monomial;
    if not member(j, idx) then return 0;
    if i != j and member(i, idx) then return 0;
    exponent * p_(replace(position(idx, e -> e == j), i, idx)) * p_idx^(exponent-1)
);

differentiatePolynomial = (i, j, polynomial) -> (
    ans := 0;
    for monomial in terms polynomial do (
        exponentList := ((listForm monomial)#0)#0;
        coeff        := ((listForm monomial)#0)#1;
        for lsIndex from 0 to numGens-1 do (
            if exponentList#lsIndex > 0 then (
                mon             := gensR#lsIndex ^ (exponentList#lsIndex);
                monomialOverMon := new MutableList from exponentList;
                monomialOverMon#lsIndex = 0;
                monomialOverMon = exponentToMonomial toList monomialOverMon;
                ans = ans + coeff * differentiateMonomial(i, j, mon) * monomialOverMon;
            );
        );
    );
    ans
);

ls = [-22*t-11, 24*t-30, 4*t-5, 22*t+11, -12*t+15, 4*t-5, -4*t+5, -22*t-11,-24*t-47, 6*t+31, 4*t-5, 6*t+31, -12*t+15, 22*t+11, -22*t-11, -30*t-1,-22*t-11, 24*t+47, 9*t+8, -17*t+79, 17*t-2, -20*t+25, -3*t-54, -9*t-8,17*t-2, -22*t-11, 12*t-15, 37*t+50, -22*t-11, -4*t+5, -28*t+35, -21*t-70,-77, 56*t+7, 42*t+63, -12*t+15, -6*t-31, 12*t-15, 4*t-5, -4*t+5, -12*t+15,6*t+31, -4*t+5, 24*t-30, 32*t+37, -17*t+2, -3*t-54, 17*t-2, 37*t+50,-17*t+2, -5*t-13, 17*t-2, 4*t-5, -4*t+5, 22*t+11, -35*t-14, 22*t+11,-3*t-54, 17*t-2, 24*t+47, -12*t+15, -t-18, 12*t-15, -4*t+5, 17*t-2,-22*t-11, -6*t-31, 4*t-5, 17*t-2, -4*t+5, 9*t+8, 77, -35*t-14, -21*t-70,21*t-7, 56*t+7, 14*t+21, 4*t-5, -5*t-13, -17*t+2, 12*t-15, 9*t+8, -17*t+2,28*t-35, 6*t+31, -4*t+5, 5*t+13, -4*t+5, 6*t+31, 4*t-5, 12*t-15, -12*t+15,-12*t+15, -32*t-37, 12*t-15, 32*t+37, -4*t+5, 11*t+44, 12*t-15, -22*t-11,17*t-2, 4*t-5, 6*t+31, -4*t+5, -21*t+7, 30*t+1, -4*t+5, -22*t-11,-11*t-44, -24*t-47, -37*t-50, 6*t+31, 42*t+63, -28*t+35, -35*t-14,-14*t-21, 21*t-7, 14*t+21, 14*t+21, 77];
f = sum(for i from 0 to 119 list ls_i * (gens R)_i);


-- Build list of Lie derivative generators using append (no nested for..list)
gensIlist = {};
for i from 0 to n-1 do
    gensIlist = append(gensIlist, differentiatePolynomial(i, i, f));
for i from 0 to n-1 do
    for j from i+1 to n-1 do (
        gensIlist = append(gensIlist, differentiatePolynomial(i, j, f));
        gensIlist = append(gensIlist, differentiatePolynomial(j, i, f));
    );
print("Number of Lie derivative generators: " | toString(#gensIlist));  -- should be 100

-- Hardcoded basis of J_1 (verified over finite field)
basisJ1R = {
    p_(1,6,9), p_(2,6,9), p_(3,6,9), p_(4,6,9), p_(5,6,9),
    p_(0,7,9), p_(1,7,9), p_(2,7,9), p_(3,7,9), p_(4,7,9),
    p_(5,7,9), p_(6,7,9), p_(0,8,9), p_(1,8,9), p_(2,8,9),
    p_(3,8,9), p_(4,8,9), p_(5,8,9), p_(6,8,9), p_(7,8,9)
};

-- All 120 monomials in fixed order
allMons = flatten entries matrix {gens R};

-- Projection matrix: [I_1 cols | basis indicators]^{-1}, take last 20 rows
Irows    = apply(gensIlist, g -> apply(allMons, m -> coefficient(m, g)));
Imat     = matrix(K, Irows);                                       -- 100x120
basisRows = apply(basisJ1R, b -> apply(allMons, m -> if m == b then 1_K else 0_K));
basisMat = transpose matrix(K, basisRows);                         -- 120x20
fullMat  = (transpose Imat) | basisMat;                           -- 120x120
projMat  = (inverse fullMat)^{100..119};                          -- 20x120

-- A_7 generator matrices for V_10 (Atlas X3: vv=b, ww=B)
GENa = matrix(K, {
    {0, 1, 0, 0, 0, 0, 0, 0, 0, 0},
    {0, 0, 0, 1, 0, 0, 0, 0, 0, 0},
    {0, 0, 0, 0, 0, 1, 0, 0, 0, 0},
    {1, 0, 0, 0, 0, 0, 0, 0, 0, 0},
    {0, 0, 0, 0, 0, 0, 0, 0, 1, 0},
    {1, -ww/2, -vv-ww/2, ww/2, 0, vv/2-ww/4, -ww/2, -vv/2-ww/4, -ww/2, -vv-ww/2},
    {1, -ww/2, -ww/2, -vv-ww/2, 1, 3*vv/2+3*ww/4, -ww/2, vv/2+3*ww/4, -ww/2, -vv-ww/2},
    {0, ww, 0, vv, -1, 1, -1, -ww, -vv, vv},
    {-2*vv-ww, vv+3*ww/2, vv+3*ww/2, vv-ww/2, -ww, -vv/2-3*ww/4, -vv-ww/2, -vv/2+ww/4, -vv-ww/2, ww/2},
    {-vv+ww/2, vv/2-ww/4, -vv/2-3*ww/4, -3*vv/2-ww/4, -2*vv-3*ww/2, 3*vv/4-3*ww/8, -3*vv/2-5*ww/4, 3*vv/4+13*ww/8, -vv/2-3*ww/4, -vv/2+5*ww/4}
});

GENb = matrix(K, {
    {0, 0, 1, 0, 0, 0, 0, 0, 0, 0},
    {0, 0, 0, 0, 1, 0, 0, 0, 0, 0},
    {0, 0, 0, 0, 0, 0, 1, 0, 0, 0},
    {0, 0, 0, 0, 0, 0, 0, 1, 0, 0},
    {0, 0, 0, 0, 0, 0, 0, 0, 0, 1},
    {-vv-ww/2, vv/2+ww/4, vv/2+ww/4, -vv/2-3*ww/4, -ww/2, vv/4-ww/8, -vv/2-3*ww/4, -3*vv/4-ww/8, vv/2+ww/4, -vv/2-ww/4},
    {1, -ww/2, -vv-ww/2, ww/2, 0, vv/2-ww/4, -ww/2, -vv/2-ww/4, -ww/2, -vv-ww/2},
    {vv+ww/2, vv/2+3*ww/4, vv/2+3*ww/4, vv/2-ww/4, vv+ww/2, -vv/4+5*ww/8, vv/2-ww/4, -5*vv/4-11*ww/8, vv/2+3*ww/4, -vv/2-3*ww/4},
    {-2, -ww, 0, -vv, 0, 0, 0, 0, 0, 0},
    {ww, 2, ww, vv+2*ww, -vv, -vv-2*ww, -vv, -2, 1, vv+2*ww}
});

print("GENa^3 == id: " | toString (GENa^3 == id_(K^10)));
print("GENb^5 == id: " | toString (GENb^5 == id_(K^10)));

kSubsets = subsets(toList(0..n-1), k);

actWedge = (M, ijk) -> (
    sum apply(kSubsets, lmp -> (
        d := det(M^lmp_ijk);
        if d == 0_K then 0_R else sub(d, R) * p_(toSequence lmp)
    ))
);

repMatrix = (M) -> (
    cols := apply(basisJ1R, bR -> (
        ijk    := toList (baseName bR)#1;
        img    := actWedge(M, ijk);
        coeffs := apply(allMons, m -> coefficient(m, img));
        v      := transpose matrix {coeffs};
        flatten entries (projMat * v)
    ));
    transpose matrix cols
);

Ainv = inverse GENa;
Binv = inverse GENb;
classReps = {
    id_(K^10),
    GENa * Binv * GENa * GENb,                       -- 2A size 105
    GENa,                                             -- 3A size 70
    Ainv * GENb * GENa * GENb,                       -- 3B size 280
    Ainv * GENb * GENa * GENb^2,                     -- 4A size 630
    GENb,                                             -- 5A size 504
    GENa * GENb * GENa * GENb * GENa * GENb^2,       -- 6A size 210
    GENa * GENb,                                      -- 7A size 360
    Ainv * GENb                                       -- 7B size 360
};
classSizes = {1, 105, 70, 280, 630, 504, 210, 360, 360};

chiRep := apply(classReps, g -> trace repMatrix g);
print("Character of 20-dim rep:");
print chiRep;
print("Trace at identity (should be 20): " | toString chiRep#0);

conjMap = map(K, K, {-1 - K_0});
conj    = (x) -> conjMap x;
ip      = (chi) -> (1/2520) * sum apply(9, i -> classSizes#i * conj(chi#i) * chiRep#i);

chi1    = {1_K,  1,  1,  1,  1,  1,  1,  1,  1};
chiV6   = {6_K,  2,  3,  0,  0,  1, -1, -1, -1};  
chiV10  = {10_K,-2,  1,  1,  0,  0,  1, vv, ww};
chiV10p = {10_K,-2,  1,  1,  0,  0,  1, ww, vv};
chiV14  = {14_K, 2,  2, -1,  0, -1,  2,  0,  0}; 
chiV14p = {14_K, 2, -1,  2,  0, -1, -1,  0,  0};  
chiV15  = {15_K,-1,  3,  0, -1,  0, -1,  1,  1};
chiV21  = {21_K, 1, -3,  0, -1,  1,  1,  0,  0}; 
chiV35  = {35_K,-1, -1, -1,  1,  0, -1,  0,  0};

print("n_1    = " | toString ip chi1);
print("n_V6   = " | toString ip chiV6);
print("n_V10  = " | toString ip chiV10);
print("n_V10' = " | toString ip chiV10p);
print("n_V14  = " | toString ip chiV14);
print("n_V14' = " | toString ip chiV14p);
print("n_V15  = " | toString ip chiV15);
print("n_V21  = " | toString ip chiV21);
print("n_V35  = " | toString ip chiV35);
