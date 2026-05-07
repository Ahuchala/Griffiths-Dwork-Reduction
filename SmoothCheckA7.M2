needsPackage "Resultants";
needsPackage "TensorComplexes"; -- for multiSubsets function
needsPackage "Schubert2"; -- for Hodge number verification

allowableThreads = 8;
n = 10;
k = 3;

K = ZZ/113;
z = 49
u = z + z^2 + z^4


d = 1;

-- access generators like p_(0,2)

-- R = K[p_(0,0) .. p_(n-1,n-1)]

pluckerIdeal = Grassmannian(k-1,n-1,CoefficientRing=>K);
R = ring pluckerIdeal;


-- ls = [11,-12*z^4 - 12*z^2 - 12*z - 18,6*z^4 + 6*z^2 + 6*z + 9,-2*z^4 - 2*z^2 - 2*z - 3,-3*z^4 - 3*z^2 - 3*z - 10,6*z^4 + 6*z^2 + 6*z + 9,-11,8*z^4 + 8*z^2 + 8*z + 1,-2*z^4 - 2*z^2 - 2*z - 3,-2*z^4 - 2*z^2 - 2*z - 3,8*z^4 + 8*z^2 + 8*z + 1,10*z^4 + 10*z^2 + 10*z + 15,-8*z^4 - 8*z^2 - 8*z - 1,-15*z^4 - 15*z^2 - 15*z - 6,2*z^4 + 2*z^2 + 2*z + 3,11,-11,-z^4 - z^2 - z + 4,-2*z^4 - 2*z^2 - 2*z - 3,10*z^4 + 10*z^2 + 10*z - 7,2*z^4 + 2*z^2 + 2*z + 3,11,-6*z^4 - 6*z^2 - 6*z - 9,8*z^4 + 8*z^2 + 8*z + 1,-6*z^4 - 6*z^2 - 6*z - 9,-6*z^4 - 6*z^2 - 6*z - 9,14*z^4 + 14*z^2 + 14*z + 21,3*z^4 + 3*z^2 + 3*z + 10,-8*z^4 - 8*z^2 - 8*z - 1,-6*z^4 - 6*z^2 - 6*z - 9,-3*z^4 - 3*z^2 - 3*z + 1,22*z^4 + 22*z^2 + 22*z + 11,11,-2*z^4 - 2*z^2 - 2*z - 3,-4*z^4 - 4*z^2 - 4*z - 17,12*z^4 + 12*z^2 + 12*z - 15,-11,2*z^4 + 2*z^2 + 2*z + 3,6*z^4 + 6*z^2 + 6*z + 9,-15*z^4 - 15*z^2 - 15*z - 6,-6*z^4 - 6*z^2 - 6*z - 9,-3*z^4 - 3*z^2 - 3*z - 10,3*z^4 + 3*z^2 + 3*z - 1,-10*z^4 - 10*z^2 - 10*z + 7,11,-3*z^4 - 3*z^2 - 3*z - 10,2*z^4 + 2*z^2 + 2*z + 3,6*z^4 + 6*z^2 + 6*z + 9,8*z^4 + 8*z^2 + 8*z + 1,10*z^4 + 10*z^2 + 10*z - 7,9*z^4 + 9*z^2 + 9*z - 14,2*z^4 + 2*z^2 + 2*z + 3,2*z^4 + 2*z^2 + 2*z + 3,6*z^4 + 6*z^2 + 6*z + 9,-17*z^4 - 17*z^2 - 17*z + 2,-15*z^4 - 15*z^2 - 15*z - 6,-2*z^4 - 2*z^2 - 2*z - 3,6*z^4 + 6*z^2 + 6*z - 13,-3*z^4 - 3*z^2 - 3*z - 10,z^4 + z^2 + z + 18,-3*z^4 - 3*z^2 - 3*z - 10,-3*z^4 - 3*z^2 - 3*z + 1,2*z^4 + 2*z^2 + 2*z + 3,14*z^4 + 14*z^2 + 14*z + 21,8*z^4 + 8*z^2 + 8*z + 1,4*z^4 + 4*z^2 + 4*z + 17,11,6*z^4 + 6*z^2 + 6*z + 9,-5*z^4 - 5*z^2 - 5*z - 2,-2*z^4 - 2*z^2 - 2*z - 3,z^4 + z^2 + z - 4,11,-12*z^4 - 12*z^2 - 12*z - 18,-3*z^4 - 3*z^2 - 3*z - 10,6*z^4 + 6*z^2 + 6*z + 9,-22*z^4 - 22*z^2 - 22*z - 11,-3*z^4 - 3*z^2 - 3*z - 10,-3*z^4 - 3*z^2 - 3*z - 10,2*z^4 + 2*z^2 + 2*z + 3,-2*z^4 - 2*z^2 - 2*z - 3,-17*z^4 - 17*z^2 - 17*z + 2,-2*z^4 - 2*z^2 - 2*z - 3,3*z^4 + 3*z^2 + 3*z + 10,11,z^4 + z^2 + z + 18,25*z^4 + 25*z^2 + 25*z + 21,2*z^4 + 2*z^2 + 2*z + 3,6*z^4 + 6*z^2 + 6*z - 13,11,-6*z^4 - 6*z^2 - 6*z + 13,-6*z^4 - 6*z^2 - 6*z - 31,9*z^4 + 9*z^2 + 9*z - 14,2*z^4 + 2*z^2 + 2*z + 3,11*z^4 + 11*z^2 + 11*z,2*z^4 + 2*z^2 + 2*z + 3,-5*z^4 - 5*z^2 - 5*z - 13,8*z^4 + 8*z^2 + 8*z + 1,-6*z^4 - 6*z^2 - 6*z - 9,-11*z^4 - 11*z^2 - 11*z,-4*z^4 - 4*z^2 - 4*z + 5,12*z^4 + 12*z^2 + 12*z - 15,3*z^4 + 3*z^2 + 3*z + 10,z^4 + z^2 + z - 4,-6*z^4 - 6*z^2 - 6*z - 9,-11,-6*z^4 - 6*z^2 - 6*z - 31,2*z^4 + 2*z^2 + 2*z + 3,z^4 + z^2 + z - 4,-10*z^4 - 10*z^2 - 10*z + 7,-5*z^4 - 5*z^2 - 5*z - 13,z^4 + z^2 + z + 18,4*z^4 + 4*z^2 + 4*z - 5,5*z^4 + 5*z^2 + 5*z + 13,3*z^4 + 3*z^2 + 3*z + 10,-9*z^4 - 9*z^2 - 9*z + 14,4*z^4 + 4*z^2 + 4*z - 5,-14*z^4 - 14*z^2 - 14*z - 21,8*z^4 + 8*z^2 + 8*z + 1,4*z^4 + 4*z^2 + 4*z - 5,22*z^4 + 22*z^2 + 22*z + 11]

ls1 = [11, -18, 9, -3, -10, 9, -11, 1, -3, -3, 1, 15, -1, -6, 3, 11, -11, 4, -3, -7, 3, 11, -9, 1, -9, -9, 21, 10, -1, -9, 1, 11, 11, -3, -17, -15, -11, 3, 9, -6, -9, -10, -1, 7, 11, -10, 3, 9, 1, -7, -14, 3, 3, 9, 2, -6, -3, -13, -10, 18, -10, 1, 3, 21, 1, 17, 11, 9, -2, -3, -4, 11, -18, -10, 9, -11, -10, -10, 3, -3, 2, -3, 10, 11, 18, 21, 3, -13, 11, 13, -31, -14, 3, 0, 3, -13, 1, -9, 0, 5, -15, 10, -4, -9, -11, -31, 3, -4, 7, -13, 18, -5, 13, 10, 14, -5, -21, 1, -5, 11];
ls2 = [0, -12, 6, -2, -3, 6, 0, 8, -2, -2, 8, 10, -8, -15, 2, 0, 0, -1, -2, 10, 2, 0, -6, 8, -6, -6, 14, 3, -8, -6, -3, 22, 0, -2, -4, 12, 0, 2, 6, -15, -6, -3, 3, -10, 0, -3, 2, 6, 8, 10, 9, 2, 2, 6, -17, -15, -2, 6, -3, 1, -3, -3, 2, 14, 8, 4, 0, 6, -5, -2, 1, 0, -12, -3, 6, -22, -3, -3, 2, -2, -17, -2, 3, 0, 1, 25, 2, 6, 0, -6, -6, 9, 2, 11, 2, -5, 8, -6, -11, -4, 12, 3, 1, -6, 0, -6, 2, 1, -10, -5, 1, 4, 5, 3, -9, 4, -14, 8, 4, 22];

f = sum(for i from 0 to 119 list ls1_i * (gens R)_i) + u*sum(for i from 0 to 119 list ls2_i * (gens R)_i); 

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


singLocus = I + pluckerIdeal + ideal f;
dim singLocus == 0  