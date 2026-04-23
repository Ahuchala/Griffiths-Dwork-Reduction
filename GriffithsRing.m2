needsPackage "Resultants";
needsPackage "TensorComplexes"; -- for multiSubsets function
needsPackage "WeilDivisors";
needsPackage "Schubert2"; -- for Hodge number verification
needsPackage "Cyclotomic"
allowableThreads = 8;
n = 6;
k = 2;
-- K = cyclotomicField(3);
-- w1 = K_0;
-- z = K_0;
-- z = v + v^2 + v^4;
-- K = QQ;
-- K = ZZ/997;
-- z = 304 -- 3rd root of unity mod 997
-- w1 = z
K = ZZ/97;
-- z = K_0;
-- K = QQ[z]/(z^2+z+2);
-- K = ZZ/113;
-- ddd = 12;
-- z = -24;
-- z = 49;  -- 7th root of unity mod 113
-- z = z+z^2 + z^4;
-- z = 35;  -- 3rd root of unity mod 97
d = 2;
-- D_5
--r= {1, 3, 0, 6, 9, 8, 2, 5, 4, 7}
--s= {9, 4, 7, 8, 1, 6, 5, 2, 3, 0}
-- r^5 = s^2 = 1, rs = sr^-1

SYMMETRIZE = true;
ANTISYMMETRIZE = false;
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


-- f = sum(apply(gens R, i->random(0,100)*(i)^d));

randomIntPoly = (d, R) -> 
(
	g := random(d, R);
	monoms := flatten entries monomials g;
	sum apply(monoms, m -> random(100) * m)
);

-- Usage:
f = randomIntPoly(d, R);


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
-- a_0 = 0;
-- a_1 = 0;
-- a_2 = 0;
-- a_3 = 0;
-- a_4 = 0;
-- a_5 = 0;
-- a_6 = 0;
-- a_7 = 0;
-- a_8 = 0;
-- a_9 = 2;
-- a_10 = 1;

-- 960, w1^3 =1
-- ls = [3,0,2*w1 + 1,-2*w1 - 1,-w1 + 1,0,-w1 - 2,w1 - 1,-w1 + 1,2*w1 + 1,2*w1 + 4,-3*w1 - 6,-3,-w1 + 1,-3*w1,-w1 - 2,w1 - 1,w1 + 2,-w1 + 1,w1 - 1,w1 + 2,2*w1 + 1,0,-w1 + 1,-3*w1,0,3*w1,2*w1 + 1,w1 - 1,-w1 - 2,3*w1,w1 - 1,-2*w1 - 4,w1 + 2,3*w1,w1 - 1,-2*w1 - 1,3,0,2*w1 + 1,0,-2*w1 + 2,-2*w1 - 1,-3,-2*w1 - 1,2*w1 + 4,w1 + 2,-w1 - 2,0,3,5*w1 + 1,3*w1,0,-3*w1 + 3,-2*w1 - 1,0,-2*w1 + 2,2*w1 + 1,-w1 - 2,-w1 - 2,0,2*w1 - 2,-w1 - 2,w1 + 2,2*w1 + 1,-2*w1 - 4,0,3*w1 + 3,2*w1 + 1,0,0,w1 + 2,0,0,w1 + 2,-2*w1 - 4,-6,0,2*w1 + 4,-3*w1 - 3,-2*w1 - 4,2*w1 - 2,0,-3*w1 - 3,0,-2*w1 - 1,-2*w1 - 1,w1 + 2,-w1 + 1,-3,0,-w1 + 1,-3,0,0,4*w1 + 2,-4*w1 - 2,2*w1 + 4,0,0,w1 + 2,0,0,w1 + 2,-w1 + 1,-w1 - 2,2*w1 - 2,0,w1 - 1,-w1 - 2,-w1 + 1,0,-2*w1 + 2,0,-w1 + 1,2*w1 + 4,w1 - 1,-4*w1 - 2,0,-3*w1 - 3]
-- ls = {-3*z-3, 0, -z-2, z-1, -z+1, -z+1, -3*z-3, 2*z+1,3*z+3, -z+1, z-1, -4*z-2, 0, z+2, z-1, 4*z+2,-z+1, -3*z-3, 0, z-1, -z-2, 6*z+3, -z+1, -2*z-1,-4*z-2, 0, 0, -z+4, -2*z-1, z-1, 3, z-1, 4*z+2, 0,-2*z-1, 0, 3*z+3, 0, -z-2, -2*z-1, -3*z, -z-2, 3, 0,-2*z-1, -z+1, 0, 6*z+6, -z-2, 0, 3, 2*z+1, 3*z, 0,-z-2, -z-2, 2*z+1, -z-2, -2*z-4, z+2, 2*z+1,-z+1, -3, 0, 0, -z-2, z+2, -2*z-4, 0, 3*z+3, 0, z+2,2*z+1, 4*z+2, -2*z+2, 2*z+1, 0, -2*z-1, 2*z+4, 0,-4*z-2, 0, 0, z+2, z+2, -3, z-1, -2*z-1, 0, 0, 0,-3*z-6, -2*z-1, 3*z+3, 2*z+1, -z+1, -4*z-2, 0,-2*z-1, 4*z+2, 0, 2*z+4, 2*z-2, 2*z+4, -2*z-4, 3,2*z+1, 3*z, 0, z+2, -z-2, 2*z-2, z+2, -2*z-1, 0, 0,2*z+1, -4*z-2, 0, 3*z}

-- ls = {1,-1,-1,1,-1,1,1,-1,-1,1,0,-1,0,0,0,-1,1,0,0,1,-1,-1,0,0,0,0,0,-1,-1,0,0,1,-1,0,1,0,-1,-1,1,0,0,0,0,0,-1,-1,1,0,0,-1,0,0,-1,0,1,-1,0,1,0,-1,1,1,-1,0,0,-1,-1,1,-1,1,0,0,0,0,1,1,0,1,-1,1,0,0,0,-1,0,-1,-1,0,-1,0,0,-1,0,1,-1,-1,1,1,-1,0,-1,0,-1,0,0,0,0,0,0,0,1,1,-1,-1,0,0,1,-1,0,0};

--for A_7 and quadrics in  Gr(2,6)
ls = {1, 2/3, -2/3, 2/3, -2/3, 0, 2/3, -2/3, 0, 0, 2/3, -2/3, 0, 0, 0, 1, 2/3,2/3, 0, -2/3, 2/3, 0, -2/3, 0, 2/3, 0, -2/3, 0, 0, 1, 0, 2/3, -2/3, 0,2/3, -2/3, 0, 0, 2/3, -2/3, 0, 0, 1, 2/3, 2/3, 2/3, 0, 0, -2/3, 2/3, 0,0, -2/3, 0, 1, 2/3, 0, 2/3, 0, -2/3, 0, 2/3, 0, -2/3, 0, 1, 0, 0, 2/3,-2/3, 0, 0, 2/3, -2/3, 0, 1, 2/3, 2/3, 2/3, 2/3, 0, 0, 0, -2/3, 1, 2/3,2/3, 0, 2/3, 0, 0, -2/3, 1, 2/3, 0, 0, 2/3, 0, -2/3, 1, 0, 0, 0, 2/3,-2/3, 1, 2/3, 2/3, 2/3, 2/3, 1, 2/3, 2/3, 2/3, 1, 2/3, 2/3, 1, 2/3, 1}; -- 

-- ls1 = [11, -18, 9, -3, -10, 9, -11, 1, -3, -3, 1, 15, -1, -6, 3, 11, -11, 4, -3, -7, 3, 11, -9, 1, -9, -9, 21, 10, -1, -9, 1, 11, 11, -3, -17, -15, -11, 3, 9, -6, -9, -10, -1, 7, 11, -10, 3, 9, 1, -7, -14, 3, 3, 9, 2, -6, -3, -13, -10, 18, -10, 1, 3, 21, 1, 17, 11, 9, -2, -3, -4, 11, -18, -10, 9, -11, -10, -10, 3, -3, 2, -3, 10, 11, 18, 21, 3, -13, 11, 13, -31, -14, 3, 0, 3, -13, 1, -9, 0, 5, -15, 10, -4, -9, -11, -31, 3, -4, 7, -13, 18, -5, 13, 10, 14, -5, -21, 1, -5, 11]
-- ls2 = [0, -12, 6, -2, -3, 6, 0, 8, -2, -2, 8, 10, -8, -15, 2, 0, 0, -1, -2, 10, 2, 0, -6, 8, -6, -6, 14, 3, -8, -6, -3, 22, 0, -2, -4, 12, 0, 2, 6, -15, -6, -3, 3, -10, 0, -3, 2, 6, 8, 10, 9, 2, 2, 6, -17, -15, -2, 6, -3, 1, -3, -3, 2, 14, 8, 4, 0, 6, -5, -2, 1, 0, -12, -3, 6, -22, -3, -3, 2, -2, -17, -2, 3, 0, 1, 25, 2, 6, 0, -6, -6, 9, 2, 11, 2, -5, 8, -6, -11, -4, 12, 3, 1, -6, 0, -6, 2, 1, -10, -5, 1, 4, 5, 3, -9, 4, -14, 8, 4, 22]

-- f = sum(for i from 0 to 119 list ls1_i * (gens R)_i)
-- f += z * sum(for i from 0 to 119 list ls2_i * (gens R)_i)
-- f = (-3*z-3)*p_(0,1,2)+(-z-2)*p_(0,2,3)+(z-1)*p_(1,2,3)+(-z+1)*p_(      0,1,4)+(-z+1)*p_(0,2,4)+(-3*z-3)*p_(1,2,4)+(2*z+1)*p_(0,3,4)+(3*      z+3)*p_(1,3,4)+(-z+1)*p_(2,3,4)+(z-1)*p_(0,1,5)+(-4*z-2)*p_(0,      2,5)+(z+2)*p_(0,3,5)+(z-1)*p_(1,3,5)+(4*z+2)*p_(2,3,5)+(-z+1)*      p_(0,4,5)+(-3*z-3)*p_(1,4,5)+(z-1)*p_(3,4,5)+(-z-2)*p_(0,1,6)+(6*      z+3)*p_(0,2,6)+(-z+1)*p_(1,2,6)+(-2*z-1)*p_(0,3,6)+(-4*z-2)*p      _(1,3,6)+(-z+4)*p_(1,4,6)+(-2*z-1)*p_(2,4,6)+(z-1)*p_(3,4,6)+3*p      _(0,5,6)+(z-1)*p_(1,5,6)+(4*z+2)*p_(2,5,6)+(-2*z-1)*p_(4,5,6)+(3*      z+3)*p_(0,2,7)+(-z-2)*p_(0,3,7)+(-2*z-1)*p_(1,3,7)-3*z*p_(2,3,      7)+(-z-2)*p_(0,4,7)+3*p_(1,4,7)+(-2*z-1)*p_(3,4,7)+(-z+1)*p_(0,5,      7)+(6*z+6)*p_(2,5,7)+(-z-2)*p_(3,5,7)+3*p_(0,6,7)+(2*z+1)*p_(1,6,      7)+3*z*p_(2,6,7)+(-z-2)*p_(4,6,7)+(-z-2)*p_(5,6,7)+(2*z+1)*p_(      0,1,8)+(-z-2)*p_(0,2,8)+(-2*z-4)*p_(1,2,8)+(z+2)*p_(0,3,8)+(2*ww_      3+1)*p_(1,3,8)+(-z+1)*p_(2,3,8)-3*p_(0,4,8)+(-z-2)*p_(3,4,8)+(z+2      )*p_(0,5,8)+(-2*z-4)*p_(1,5,8)+(3*z+3)*p_(3,5,8)+(z+2)*p_(0,6,8      )+(2*z+1)*p_(1,6,8)+(4*z+2)*p_(2,6,8)+(-2*z+2)*p_(3,6,8)+(2*z+      1)*p_(4,6,8)+(-2*z-1)*p_(0,7,8)+(2*z+4)*p_(1,7,8)+(-4*z-2)*p_(3,7      ,8)+(z+2)*p_(6,7,8)+(z+2)*p_(0,1,9)-3*p_(0,2,9)+(z-1)*p_(1,2,9      )+(-2*z-1)*p_(0,3,9)+(-3*z-6)*p_(1,4,9)+(-2*z-1)*p_(2,4,9)+(3*ww_      3+3)*p_(3,4,9)+(2*z+1)*p_(0,5,9)+(-z+1)*p_(1,5,9)+(-4*z-2)*p_(2,5      ,9)+(-2*z-1)*p_(4,5,9)+(4*z+2)*p_(0,6,9)+(2*z+4)*p_(2,6,9)+(2*ww_      3-2)*p_(3,6,9)+(2*z+4)*p_(4,6,9)+(-2*z-4)*p_(5,6,9)+3*p_(0,7,9)+(2*      z+1)*p_(1,7,9)+3*z*p_(2,7,9)+(z+2)*p_(4,7,9)+(-z-2)*p_(5,7,9      )+(2*z-2)*p_(6,7,9)+(z+2)*p_(0,8,9)+(-2*z-1)*p_(1,8,9)+(2*z+1      )*p_(4,8,9)+(-4*z-2)*p_(5,8,9)+3*z*p_(7,8,9)



f = sum(for i from 0 to 119 list ls_i * (gens R)_i)
symF = f
-- f = symF;

-- d = (degree f)#0;
-- degf = d;
-- symF = f

-- this needs to have pluckerIdeal inside too
-- print "Smoothness check"
-- assert isSmooth(pluckerIdeal+ideal f,IsGraded=>true)

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
-- S = R/(pluckerIdeal + J);
-- S = R/(pluckerIdeal + J + antisymmetrize_ideal);

-- Hodge numbers of primitive cohomology
-- (R_f)_{(p+1)d-n} = H^{N-1-p,p}
for i from 0 to n+1 list hilbertFunction((i+1)*d - n,J)


for i from 1 to n-1 do if i == k*(n-k)/2 then print concatenate("Warning: nontrivial cokernel contribution for i =",toString i) else continue


-- e.g. 3/3 == 1
for i from 1 to n-1 do if (i==((2*n-1-d)/3) or i==((4*n-9-d)/3)) then print concatenate("Potential error with i =",toString i) else continue


print "Expected Hodge numbers:"


-- k = 3
-- n = 7

-- d = toList(d)




G = flagBundle {k,n-k}; -- secretly Gr(k,n)
-- for d from 1 to 25 list (
-- X = sectionZeroLocus(sum for i from 1 to #d list OO_G(i)); -- quadric and a cubic
X = sectionZeroLocus(OO_G(d)); 

OmG = cotangentBundle G;
OmX = cotangentBundle X;

ls = for i from 0 to floor(dim X / 2) list
    abs(chi exteriorPower(i, OmX) - chi exteriorPower(i, OmG));

if (k*(n-k) % 2 ==0) then (
    print join(ls,reverse ls);
) else (
-- include the second half, but don't repeat middle element
print (join(ls, for i from 1 to #ls-1  list ls#(#ls-i-1)));
);

-- print "Smoothness check"
-- assert isSmooth(pluckerIdeal+ideal f,IsGraded=>true)



 getBasisInJ = (deg, J) -> (
    B := basis(deg, J);
    if B == 0 then return {};
    flatten entries B
);

-- Function to get the matrix representation of a permutation acting on a basis in J
permutationMatrixInJ = (perm, basisElems, J) -> (
    -- basisElems should be a list of elements in J
    m := #basisElems;
    
    -- Lift to R, apply permutation, reduce back to J
    images := apply(basisElems, b -> (
        bLifted := lift(b, J);
        imageInR := applyPermutationToPoly(bLifted, perm);
        sub(imageInR, J)
    ));
    
    -- Express each image as a linear combination of basis elements
    coeffMatrix := {};
    for img in images do (
        imgLifted := lift(img, J);
        coeffs := apply(basisElems, b -> (
            bLifted := lift(b, J);
            coefficient(bLifted, imgLifted)
        ));
        coeffMatrix = append(coeffMatrix, coeffs);
    );
    
    transpose matrix coeffMatrix
);

-- Get basis in J at a given degree
allBases = for i from 0 to n+1 list 
(
	deg := (i+1)*d - n;
	if deg >= 0 then basis(deg, J) else 0
);

-- Then extract as needed
getBasisInJ = (deg, J) -> 
(
	i := (deg + n - d) // d;
	if i >= 0 and i < #allBases and allBases#i != 0 then
		flatten entries allBases#i
	else
		{}
);





-- Function to create direct sum of permutation matrices over all relevant degrees
permutationMatrixAllDegrees = (perm, J, n, d) -> (
  matrices := {};
  for i from 0 to n+1 do (
    deg := (i+1)*d - n;
    if deg >= 0 then (
      B := getBasisInJ(deg, J);
      if #B > 0 then (
        M := permutationMatrixInJ(perm, B, J);
        if ANTISYMMETRIZE then (
          M *= (-1)^(countInversions(perm) * (i*d-n)); -- Adjust sign based on action on f
        );
        matrices = append(matrices, M);
      );
    );
  );

  if #matrices == 0 then (
    return matrix{{0}};
  );

  directSum matrices
);

-- Collect traces
traceList := {};

for perm in permList do (
  bigM := permutationMatrixAllDegrees(perm, J, n, d);
   -- Adjust sign based on action on Omega
   if k % 2 == 1 then (
      sign := (-1)^(countInversions(perm));
      bigM *= sign;
   );
  traceList = append(traceList, trace bigM);
);

permutationMiddleDegree = (perm) -> (
  matrices := {};
  deg := 1;
    if deg >= 0 then (
      B := getBasisInJ(deg, J);
      if #B > 0 then (
        M := permutationMatrixInJ(perm, B, J);
        if ANTISYMMETRIZE then (
          M *= (-1)^(countInversions(perm) * (i*d-n)); -- Adjust sign based on action on f
        );
        matrices = append(matrices, M);
      );
  );

  if #matrices == 0 then (
    return matrix{{0}};
  );

  directSum matrices
);

traceListMiddle := {};

for perm in permList do (
  bigM := permutationMiddleDegree(perm);
   -- Adjust sign based on action on Omega
   if k % 2 == 1 then (
      sign := (-1)^(countInversions(perm));
      bigM *= sign;
   );
  traceListMiddle = append(traceListMiddle, trace bigM);
);


print permList;
print "Traces (in order of permList):";
print traceList;
print (toString symF);

print eigenvalues permutationMatrixAllDegrees(permList#3,J,n,d)
for i from 0 to #permList-1 list symF - (-1)^(countInversions permList#i)*applyPermutationToPoly(symF,permList#i)
