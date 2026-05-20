-- GriffithsRingA7.M2
--
-- Griffiths-Dwork ring computation for the linear (degree d = 1) section
-- Z = V(f) in Gr(3, 10) singled out by the A_7 symmetry of f. The defining
-- linear form f is built from the two integer coefficient lists ls1, ls2
-- and the scalar u = z + z^2 + z^4 in F_113 (z a primitive root). The
-- output is the list of graded dimensions of R / J_f relevant to the
-- primitive cohomology of Z.
--
-- Run with:  M2 GriffithsRingA7.M2
-- Companion files: A7Intersection.M2, A7IrrepDecomposition.M2, SmoothCheckA7.M2
-- Thesis reference: Chapter 5, A_7-symmetric example in Gr(3, 10).

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

ls1 = [11, -18, 9, -3, -10, 9, -11, 1, -3, -3, 1, 15, -1, -6, 3, 11, -11, 4, -3, -7, 3, 11, -9, 1, -9, -9, 21, 10, -1, -9, 1, 11, 11, -3, -17, -15, -11, 3, 9, -6, -9, -10, -1, 7, 11, -10, 3, 9, 1, -7, -14, 3, 3, 9, 2, -6, -3, -13, -10, 18, -10, 1, 3, 21, 1, 17, 11, 9, -2, -3, -4, 11, -18, -10, 9, -11, -10, -10, 3, -3, 2, -3, 10, 11, 18, 21, 3, -13, 11, 13, -31, -14, 3, 0, 3, -13, 1, -9, 0, 5, -15, 10, -4, -9, -11, -31, 3, -4, 7, -13, 18, -5, 13, 10, 14, -5, -21, 1, -5, 11];
ls2 = [0, -12, 6, -2, -3, 6, 0, 8, -2, -2, 8, 10, -8, -15, 2, 0, 0, -1, -2, 10, 2, 0, -6, 8, -6, -6, 14, 3, -8, -6, -3, 22, 0, -2, -4, 12, 0, 2, 6, -15, -6, -3, 3, -10, 0, -3, 2, 6, 8, 10, 9, 2, 2, 6, -17, -15, -2, 6, -3, 1, -3, -3, 2, 14, 8, 4, 0, 6, -5, -2, 1, 0, -12, -3, 6, -22, -3, -3, 2, -2, -17, -2, 3, 0, 1, 25, 2, 6, 0, -6, -6, 9, 2, 11, 2, -5, 8, -6, -11, -4, 12, 3, 1, -6, 0, -6, 2, 1, -10, -5, 1, 4, 5, 3, -9, 4, -14, 8, 4, 22];

f = sum(for i from 0 to 119 list ls1_i * (gens R)_i) + u*sum(for i from 0 to 119 list ls2_i * (gens R)_i);



gensR = gens R;
numGens = #gensR;


countInversions = (perm) -> (
    ans := 0;
    for i from 0 to #perm-2 do (
        for j from i+1 to #perm-1 do (
            if perm#j < perm#i then ans = ans + 1;
        );
    );
    ans
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


gensI = gens I;

if (# (entries gens I)#0 != n^2) then error (
    print "Warning: Jacobian ideal does not have expected number of generators";
    exit 1;
) ;



J = R /  (I + pluckerIdeal);


-- Hodge numbers of primitive cohomology
-- (R_f)_{(p+1)d-n} = H^{N-1-p,p}
for i from 0 to n+1 list hilbertFunction((i+1)*d - n,J)


for i from 1 to n-1 do if i == k*(n-k)/2 then print concatenate("Warning: nontrivial cokernel contribution for i =",toString i) else continue


-- e.g. 3/3 == 1
for i from 1 to n-1 do if (i==((2*n-1-d)/3) or i==((4*n-9-d)/3)) then print concatenate("Potential error with i =",toString i) else continue


print "Expected Hodge numbers:"



G = flagBundle {k,n-k}; -- secretly Gr(k,n)
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

-- print basis with
for p from 10 to 12 list basis(p*d -n,J)