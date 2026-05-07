needsPackage "Resultants";
needsPackage "TensorComplexes"; -- for multiSubsets function
needsPackage "WeilDivisors";
needsPackage "Schubert2"; -- for Hodge number verification
needsPackage "Cyclotomic"

allowableThreads = 8;
n = 10;
k = 3;
K = QQ;


d = 1;

-- access generators like p_(0,2)

-- R = K[p_(0,0) .. p_(n-1,n-1)]

pluckerIdeal = Grassmannian(k-1,n-1,CoefficientRing=>K);
R = ring pluckerIdeal;

f=p_(0,1,2)-p_(0,1,4)+p_(0,1,5)+p_(0,1,8)-p_(0,2,3)-p_(0,2,4)+p_(0,2,6)-p_(0,3,9)+p_(0,4,5)-p_(0,4,6)-p_(0,4,7)+p_(0,5,6)+p_(0,5,7)+p_(0,5,8)+p_(0,6,7)-p_(0,7,9)-p_(0,8,9)-p_(1,2,5)+p_(1,2,7)+p_(1,2,8)+p_(1,3,4)-p_(1,3,5)+p_(1,3,7)-p_(1,3,9)+p_(1,5,7)+p_(1,5,8)+p_(1,8,9)+p_(2,3,4)-p_(2,3,8)+p_(2,4,5)-p_(2,4,7)+p_(2,5,6)+p_(2,6,7)+p_(2,6,8)+p_(3,4,5)-p_(3,5,7)+p_(5,7,9)+p_(5,8,9)-p_(6,8,9)-p_(7,8,9);



-- access generators like p_(0,2)

-- R = K[p_(0,0) .. p_(n-1,n-1)]

pluckerIdeal = Grassmannian(k-1,n-1,CoefficientRing=>K);
R = ring pluckerIdeal;




gensR = gens R;
numGens = #gensR;


countInversions = (perm) -> (
    lenPerm = #perm;
    ans = 0;
    for i from 0 to lenPerm-1 do (
  for j from i+1 to lenPerm-1 do (
if perm#j < perm#i then (
    ans += 1;
);
  );
    );
    return ans;
);

-- (1,2,3) -> false, (2,2,3) -> true
hasDuplicates = (ls) -> (
    return unique ls != ls;
);

-- define all p_I, not just for I increasing (i.e. the k wedges of x_i)
for inds in multiSubsets(n,k) do (
	-- set all p_ii to zero
	if (hasDuplicates(inds)) then (
  for perm in permutations(inds) do (
p_(toSequence perm) = 0;
  );
    ) else for perm in permutations(inds) do (
		-- e.g. set p_(i,j,k) = -p_(j,i,k)
  p_(toSequence perm) = (-1)^(countInversions(perm)) * p_(toSequence inds);
    );
);


randomIntPoly = (d, R) -> 
(
	g := random(d, R);
	monoms := flatten entries monomials g;
	sum apply(monoms, m -> random(100) * m)
);

-- Usage:
-- f = randomIntPoly(d, R);


-- scan(11, i -> a_i = random(-100, 100))


inversePerm = (perm) -> (
	n := #perm;
	inv := new MutableList from toList(0..n-1);
	for i from 0 to n-1 do (
		inv#(perm#i) = i;
	);
	toList inv
);

countInversions = (perm) -> (
    ans := 0;
    for i from 0 to #perm-2 do (
        for j from i+1 to #perm-1 do (
            if perm#j < perm#i then ans = ans + 1;
        );
    );
    ans
);

-- Build lookup table once
varLookup := hashTable apply(gens R, v -> (
    toList (baseName v)#1 => v
));

applyPermutationToPoly = (f, perm) -> (
    subList := apply(gens R, v -> (
        indices := toList (baseName v)#1;
        newIndices := apply(indices, i -> perm#i);
        sortedIndices := sort newIndices;
        sign := (-1)^(countInversions(newIndices));
        v => sign * varLookup#sortedIndices
    ));
    sub(f, subList)
);

sumOverPermutations = (f, permList) -> (
  if ANTISYMMETRIZE then (
    return sum apply(permList, perm -> (-1)^(countInversions(perm)) * applyPermutationToPoly(f, perm))
  );
  if not ANTISYMMETRIZE then (
    return sum apply(permList, perm -> applyPermutationToPoly(f, perm))
  );
);

print "Divisibility check"

-- check Fern and my vanishings
for t from 1 to min(n-1,n //d) do (
    print(t);
    assert not (n % (t*d)==0 and k*d*t % n == 0)
);


assert (gcd(k,n//d) == 1);
assert (gcd(n-k,n//d) == 1); -- probably redundant?
assert (n<5 or n % 2 == 0 or (k!=2 and k!= n-2) or (n+1)//2 % d != 0);




-- e.g. p_(0,1) -> (0,1)
getIndex = (mon) -> (
    return (baseName mon)#1;
);

-- e.g. 5*p_(0,1)*p_(1,2)^2 -> ({1,0,2,0,0,...,0})
getMonomials = (polynomial) -> (
    return exponents (polynomial);
);

-- e.g. 5* p_(0,1)*p_(1,2)^2 -> (| p_(0,1)p_(1,2)^2 |, {3} | 5 |)
getCoefficients = (polynomial) -> (
    return coefficients(polynomial);
);

exponentToMonomial = (ls) -> (
    return product (for i from 0 to (numGens-1) list (gensR#i) ^ (ls#i));
);

-- this only works for p_I^j, not products
differentiateMonomial = (i,j,mon) -> (
    monomialIndex = (exponents (mon))#0;
    -- silly way to find the single exponent that shows up
    exponent = sum(monomialIndex);
    -- select the entry 
    ind = position((exponents mon)#0,lambda->lambda==exponent);
    monomial = gensR#ind;
    ls = getIndex(monomial);
    if (not member(j,ls)) then (
  return 0;
    );
    if (i!=j) and( member(i,ls)) then (
  return 0;
    );

    -- set j to i (replace copies then edits a list)
    return exponent * p_(replace(position(ls, lambda->lambda==j),i,ls)) * p_ls^(exponent-1);
);


differentiatePolynomial = (i,j,polynomial) -> (
    ans = 0;
    mons = terms(polynomial);
    for monomial in mons do (
  exponentList = ((listForm monomial)#0)#0;
  coeff = ((listForm monomial)#0)#1;
  
  for lsIndex from 0 to (numGens -1) do (
if ((exponentList#lsIndex)>0) then (
    mon = (gensR#lsIndex) ^(exponentList#lsIndex);
    -- this is an annoying way to implement the product rule
    monomialOverMon = new MutableList from exponentList;
    monomialOverMon#lsIndex = 0;
    monomialOverMon = exponentToMonomial(toList monomialOverMon);
    ans +=  coeff * differentiateMonomial(i,j,mon) * monomialOverMon;
);
  );
    );
    return ans;

);




-- Jacobian ideal I
I = ideal flatten (flatten for i from 0 to n-1 list differentiatePolynomial(i,i,f), 
    flatten flatten for i from 0 to n-1 list (
	for j from i+1 to n-1 list (
		{differentiatePolynomial(i,j,f),
		differentiatePolynomial(j,i,f)}
		-- differentiatePolynomial(i,i,f)-differentiatePolynomial(j,j,f)}
	)
));

-- I += ideal flatten for i from 0 to n-1 list differentiatePolynomial(i,i,f)

-- I = trim I;

gensI = gens I;

if (# (entries gens I)#0 != n^2) then error (
    print "Warning: Jacobian ideal does not have expected number of generators";
    exit 1;
) ;



J = R /  (I + pluckerIdeal);




-- PSL(2,11) generators on V_10
Amat = matrix(QQ, {
    {-1, 2, 0, 1, 0,-1, 2,-1, 1,-1},
    {-1, 1, 1, 0, 0,-1, 1,-1, 0, 0},
    { 0, 1, 0, 0,-1,-1, 0, 0, 0,-1},
    { 0, 0, 1, 0, 1,-1, 0,-1, 1, 1},
    {-1, 0, 1, 0, 0,-1, 0, 0, 0, 1},
    { 0, 1, 0, 0,-1,-1, 1,-1, 0,-1},
    { 0, 1,-1, 1,-1, 0, 1, 0, 0,-1},
    { 0, 0, 0, 1, 0, 0, 0, 0, 0, 0},
    { 1,-1,-1, 0, 0, 1,-1, 0, 0,-1},
    { 0, 0, 0, 0, 0, 1, 0, 0, 0, 0}});

Bmat = matrix(QQ, {
    {-1, 2, 1, 0, 0,-2, 2,-1, 1, 0},
    { 0, 1, 0, 0,-1,-1, 1,-1, 0,-1},
    { 0, 1, 0, 0, 0, 0, 0, 0, 0, 0},
    { 1,-1,-1,-1, 0, 1,-2, 1, 0, 0},
    { 0, 0, 0, 0, 0,-1, 0,-1, 0, 0},
    { 0, 0, 0, 0, 0, 1, 0, 0, 0, 0},
    {-1, 1, 1, 1, 1,-1, 2,-1, 1, 1},
    {-1, 2, 0, 1, 0,-2, 2,-1, 1, 0},
    {-1, 1, 0, 0,-1, 0, 0, 1, 0, 0},
    { 0, 0, 0, 0, 0, 0, 1, 0, 0, 0}});

-- k-subsets of {0..n-1}, ordered to match Plücker variable ordering in R
kSubsets = subsets(toList(0..n-1), k);

-- Wedge^k action of a 10x10 matrix M on p_(ijk): coefficient of p_(lmp)
-- is the 3x3 minor of M with rows lmp, columns ijk
actWedge = (M, ijk) -> (
    sum apply(kSubsets, lmp -> (
        d := det(M^lmp_ijk);
        if d == 0_QQ then 0_R else sub(d, R) * p_(toSequence lmp)
    ))
);

-- Lift basis of J_1 to R
basisJ1  = flatten entries basis(1, J);
basisJ1R = apply(basisJ1, b -> lift(b, R));

-- 20x20 representation matrix for a group element given as a 10x10 matrix
-- Column i = coordinates of image of b_i in the basis
repMatrix = (M) -> (
    cols := apply(basisJ1R, bR -> (
        ijk  := toList (baseName bR)#1;
        img  := actWedge(M, ijk);
        imgR := lift(sub(img, J), R);
        apply(basisJ1R, bj -> lift(coefficient(bj, imgR), QQ))
    ));
    transpose matrix cols
);

rhoA = repMatrix Amat;
rhoB = repMatrix Bmat;

print("trace rhoA = " | toString trace rhoA);
print("trace rhoB = " | toString trace rhoB);

-- Sanity: orders of generators
print("rhoA^5 == id: " | toString (rhoA^5 == id_(QQ^20)));
print("rhoB^3  == id: " | toString (rhoB^3  == id_(QQ^20)));

-- Class representatives from character table
Ainv = inverse Amat;
Binv = inverse Bmat;
classReps = {
    id_(QQ^10),
    Binv * Amat * Bmat * Ainv * Binv * Ainv^2,   -- b^{-1}aba^{-1}b^{-1}a^{-2}
    Binv * Ainv,                                    -- b^{-1}a^{-1}
    Amat * Bmat * Ainv * Binv * Ainv^2 * Bmat,    -- aba^{-1}b^{-1}a^{-2}b
    Binv,                                           -- b^{-1}
    Ainv^2 * Binv * Ainv^2,                        -- a^{-2}b^{-1}a^{-2}
    Amat,                                           -- a
    Amat^2                                          -- a^2
};
classSizes = {1_QQ, 60, 60, 55, 110, 110, 132, 132};

chiRep := apply(classReps, g -> lift(trace repMatrix g, QQ));
print("Character of 20-dim rep at each class:");
print chiRep;

-- Decompose using inner product <chi_rep, chi_i> = (1/660) sum_C |C| chi_i(C) chiRep(C)
-- For complex conjugate pairs (V5,V5*) and (V12,V12*) we use their rational sum
-- since any rational rep has equal multiplicities for conjugate pairs
ip = (chi) -> (1/660_QQ) * sum apply(8, i -> classSizes#i * chi#i * chiRep#i);

chi1      = {1_QQ,   1,  1,  1,   1,  1,  1,  1};
chiV5sum  = {10_QQ, -1, -1,  2,  -2,  2,  0,  0}; -- chi_{V5} + chi_{V5*}
chiV10    = {10_QQ, -1, -1, -2,   1,  1,  0,  0};
chiV10p   = {10_QQ, -1, -1,  2,   1, -1,  0,  0};
chiV11    = {11_QQ,  0,  0, -1,  -1, -1,  1,  1};
chiV12sum = {24_QQ,  2,  2,  0,   0,  0, -1, -1}; -- chi_{V12} + chi_{V12*}

print("n_1           = " | toString ip chi1);
print("n_{V5}=n_{V5'}= " | toString ((ip chiV5sum) / 2));
print("n_{V10}       = " | toString ip chiV10);
print("n_{V10'}      = " | toString ip chiV10p);
print("n_{V11}       = " | toString ip chiV11);
print("n_{V12}=n_{V12'}=" | toString ((ip chiV12sum) / 2));