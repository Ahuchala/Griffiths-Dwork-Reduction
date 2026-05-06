needsPackage "Resultants";
needsPackage "TensorComplexes"; -- for multiSubsets function
needsPackage "Divisor";
needsPackage "Schubert2"; -- for Hodge number verification
needsPackage "Cyclotomic"
allowableThreads = 8;
n = 10;
k = 3;
-- K = cyclotomicField(7);
-- v = K_0;
-- z = v + v^2 + v^4;
-- K = QQ;
K = QQ[z]/(z^2+z+2);

d = 1;



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
-- f = randomIntPoly(d, R);

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


-- f = sum(for i from 0 to 119 list ls1_i * (gens R)_i)
-- f += z * sum(for i from 0 to 119 list ls2_i * (gens R)_i)
ls = {4*z+9, -12*z-6, -2*z-1, -4*z-9, 6*z+3, -2*z-1, 2*z+1, 4*z+9, -2*z+13, 4*z-5, -2*z-1, 4*z-5, 6*z+3, -4*z-9, 4*z+9, 8*z+11, 4*z+9, 2*z-13, -z-4, 19*z-1, -5*z-6, 10*z+5, -9*z+6, z+4, -5*z-6, 4*z+9, -6*z-3, -z-18, 4*z+9, 2*z+1, 14*z+7, -7*z+14, -14*z+7, -14*z-21, -21, 6*z+3, -4*z+5, -6*z-3, -2*z-1, 2*z+1, 6*z+3, 4*z-5, 2*z+1, -12*z-6, -2*z-15, 5*z+6, -9*z+6, -5*z-6, -z-18, 5*z+6, -z+3, -5*z-6, -2*z-1, 2*z+1, -4*z-9, 7*z+14, -4*z-9, -9*z+6, -5*z-6, 2*z-13, 6*z+3, -3*z+2, -6*z-3, 2*z+1, -5*z-6, 4*z+9, -4*z+5, -2*z-1, -5*z-6, 2*z+1, -z-4, 14*z-7, 7*z+14, -7*z+14, -7*z-7, -14*z-21, -7, -2*z-1, -z+3, 5*z+6, -6*z-3, -z-4, 5*z+6, -14*z-7, 4*z-5, 2*z+1, z-3, 2*z+1, 4*z-5, -2*z-1, -6*z-3, 6*z+3, 6*z+3, 2*z+15, -6*z-3, -2*z-15, 2*z+1, 5*z-8, -6*z-3, 4*z+9, -5*z-6, -2*z-1, 4*z-5, 2*z+1, 7*z+7, -8*z-11, 2*z+1, 4*z+9, -5*z+8, -2*z+13, z+18, 4*z-5, -21, 14*z+7, 7*z+14, 7, -7*z-7, -7, -7, 14*z-7}
f = sum(for i from 0 to 119 list ls_i * (gens R)_i)



symF = f


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

u = {{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,1}};
u = transpose matrix(K, u);


b = z
B = -1-b
r = matrix(K,{{0,1,0,0,0,0,0,0,0,0},{0,0,0,1,0,0,0,0,0,0},{0,0,0,0,0,1,0,0,0,0},{1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,1,0},{1,-1/2*B,-b-1/2*B,1/2*B,0,1/2*b-1/4*B,-1/2*B,-1/2*b-1/4*B,-1/2*B,  -b-1/2*B},{1,-1/2*B,-1/2*B,-b-1/2*B,1,3/2*b+3/4*B,-1/2*B,1/2*b+3/4*B,-1/2*B,  -b-1/2*B},{0,B,0,b,-1,1,-1,-B,-b,b},{-2*b-B,b+3/2*B,b+3/2*B,b-1/2*B,-B,-1/2*b-3/4*B,-b-1/2*B,-1/2*b+1/4*B,  -b-1/2*B,1/2*B},{-b+1/2*B,1/2*b-1/4*B,-1/2*b-3/4*B,-3/2*b-1/4*B,-2*b-3/2*B,3/4*b-3/8*B,  -3/2*b-5/4*B,3/4*b+13/8*B,-1/2*b-3/4*B,-1/2*b+5/4*B}});

s = matrix(K,{{0,0,1,0,0,0,0,0,0,0},{0,0,0,0,1,0,0,0,0,0},{0,0,0,0,0,0,1,0,0,0},{0,0,0,0,0,0,0,1,0,0},{0,0,0,0,0,0,0,0,0,1},{-b-1/2*B,1/2*b+1/4*B,1/2*b+1/4*B,-1/2*b-3/4*B,-1/2*B,1/4*b-1/8*B,  -1/2*b-3/4*B,-3/4*b-1/8*B,1/2*b+1/4*B,-1/2*b-1/4*B},{1,-1/2*B,-b-1/2*B,1/2*B,0,1/2*b-1/4*B,-1/2*B,-1/2*b-1/4*B,-1/2*B,  -b-1/2*B},{b+1/2*B,1/2*b+3/4*B,1/2*b+3/4*B,1/2*b-1/4*B,b+1/2*B,-1/4*b+5/8*B,  1/2*b-1/4*B,-5/4*b-11/8*B,1/2*b+3/4*B,-1/2*b-3/4*B},{-2,-B,0,-b,0,0,0,0,0,0},{B,2,B,b+2*B,-b,-b-2*B,-b,-2,1,b+2*B}});


AAA = exteriorPower(3,r);
BBB = exteriorPower(3,s);



M = last coefficients generators I
M = substitute(M,K)
trace ((AAA*M)//M)



proj = (G) -> trace((G*M)//M);

20                                                        -- C1: 1
proj(AAA * inverse(BBB) * AAA * BBB)                      -- C2: ab^{-1}ab
proj(AAA)                                                 -- C3: a
proj(AAA*BBB*AAA*BBB*AAA*BBB^2)                          -- C4: ababab^2
proj(inverse(AAA)*BBB*AAA*BBB^2)                         -- C5: a^{-1}bab^2
proj(BBB)                                                 -- C6: b
proj(inverse(AAA)*BBB*AAA*BBB)                           -- C7: a^{-1}bab
proj(AAA*BBB)                                             -- C8: ab