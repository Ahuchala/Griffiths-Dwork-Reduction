needsPackage "Resultants";
needsPackage "TensorComplexes"; -- for multiSubsets function
needsPackage "WeilDivisors";
needsPackage "Schubert2"; -- for Hodge number verification

allowableThreads = 8;
n = 5;
k = 2;

-- K = QQ;
K = ZZ/97; -- enable for faster computation
d = 3;



-- access generators like p_(0,2)

-- R = K[p_(0,0) .. p_(n-1,n-1)]

pluckerIdeal = Grassmannian(k-1,n-1,CoefficientRing=>K);
R = ring pluckerIdeal;




gensR = gens R;
numGens = #gensR;






-- Make sure \varphi' of (2.2.13) is surjective
assert(2<= k and k<= n-2)


-- Check divisibility constraints 

print "Divisibility check"


-- Check assumption 2.9
assert ((n%d != 0) or  gcd(k,n//d) == 1);

-- Check assumption 2.10
assert ((k!=2 and k!= n-2) and (n+1)%(2 * d) != 0);




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

f = randomIntPoly(d, R);

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
I = ideal flatten (flatten for i from 0 to n-2 list differentiatePolynomial(i,i,f)-differentiatePolynomial(i+1,i+1,f), 
    flatten flatten for i from 0 to n-1 list (
	for j from i+1 to n-1 list (
		{differentiatePolynomial(i,j,f),
		differentiatePolynomial(j,i,f)}
	)
));
I += (f);



gensI = gens I;


-- easy necessary condition for smoothness
if (# (entries gens I)#0 != n^2) then error (
    print "Warning: Jacobian ideal does not have expected number of generators";
    exit 1;
) ;



J = R /  (I + pluckerIdeal);

-- only show nonzero elements of R/I
select(for i from 0 to k*(n-k)-1 list basis(i*d-n,J), b -> b != 0)

-- Hodge numbers of primitive cohomology
-- (R_f)_{(p+1)d-n} = H^{N-1-p,p}
for i from 0 to n+1 list hilbertFunction((i)*d - n,J)


-- for i from 1 to n-1 do if i == k*(n-k)/2 then print concatenate("Warning: nontrivial cokernel contribution for i =",toString i) else continue


-- e.g. 3/3 == 1
-- for i from 1 to n-1 do if (i==((2*n-1-d)/3) or i==((4*n-9-d)/3)) then print concatenate("Potential error with i =",toString i) else continue


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

-- print "Smoothness check"
-- assert isSmooth(pluckerIdeal+ideal f,IsGraded=>true)


qBinom = (k, n, q) -> (
    -- Compute numerator and denominator products separately before dividing
    -- [n choose k]_q = prod_{j=0}^{k-1} (1-q^{n-j}) / prod_{j=0}^{k-1} (1-q^{j+1})
    num := product(k, j -> 1 - q^(n - j));
    den := product(k, j -> 1 - q^(j + 1));
    num // den
);

-- computes H^N_prim or H^{N-1}_prim, if N even or odd, respectively
primCohomGr = (k, n) -> (
    N    := k * (n - k);
    halfN := N // 2;
    R    := QQ[q];
    f    := (1 - q) * qBinom(k, n, q);
    coefficient(q^halfN, f)
);


if primCohomGr(k,n) >0 then (
  if k*(n-k) % 2 == 0 then (
    -- contribution from H^N_prim(Gr(k,n)), when N even
      print("Contribution to (R/J_f)_{id-n} from H^N_van(Gr), with i = " | toString (k*(n-k)//2) | ": "| toString primCohomGr(k,n));
  ) else (
    -- contribution from H^(N-1)_prim(Gr(k,n)), when N odd
      print("Contribution to H^*_prim(Z) from H^{N-1}_van(Gr): " | toString primCohomGr(k,n));
  );
);