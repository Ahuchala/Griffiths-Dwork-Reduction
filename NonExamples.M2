-- verifyNonExamples.m2
--
-- Verifies the non-examples table from chapter 4. For each (k, n, d):
--   - Try to generate a smooth random polynomial f of degree d
--       d <= 2: simple "diagonal" form sum a_i g_i^d usually works
--       d >= 3: full random integer polynomial needed for smoothness
--   - Build the Jacobian ideal J_f = (f, {E_{ij}(f)})
--   - Compute dim (R/J_f)_{pd - n} for p = 1, ..., N
--   - Compute primitive Hodge numbers h^{N-p, p-1}_prim(Z) via Schubert2
--   - Print a side-by-side comparison + ready-to-paste LaTeX rows

needsPackage "Resultants";
needsPackage "TensorComplexes";
needsPackage "WeilDivisors";
needsPackage "Schubert2";

K = ZZ/97;

-- Helpers --------------------------------------------------------------

countInversions = perm -> (
    ans := 0;
    for i from 0 to #perm - 2 do
        for j from i + 1 to #perm - 1 do
            if perm#j < perm#i then ans = ans + 1;
    ans
);

hasDuplicates = ls -> unique ls != ls;

-- Sample a random polynomial of degree d in R, with each monomial coefficient
-- drawn independently from {0, ..., 99}. Use for d >= 3 -- the diagonal form
-- typically fails smoothness in that range.
randomIntPoly = (d, R) -> (
    g := random(d, R);
    monoms := flatten entries monomials g;
    sum apply(monoms, m -> random(100) * m)
);

-- LaTeX row generators -------------------------------------------------

makePrimRow = (k, n, d, primFull, N) -> (
    cells := {toString k, toString n, toString d};
    for p from 2 to 10 do (
        idx := N - p;
        val := if idx >= 0 and idx < #primFull and primFull#idx != 0
               then toString primFull#idx
               else " ";
        cells = append(cells, val);
    );
    cells = append(cells, " ");  -- trailing phantom column
    concatenate between(" & ", cells) | " \\\\"
);

makeGriffRow = (k, n, d, griffRing, issue, N) -> (
    cells := {toString k, toString n, toString d};
    for p from 2 to 10 do (
        val := if p - 1 < #griffRing and griffRing#(p - 1) != 0
               then toString griffRing#(p - 1)
               else " ";
        cells = append(cells, val);
    );
    cells = append(cells, issue);
    concatenate between(" & ", cells) | " \\\\"
);

-- Single-case verifier -------------------------------------------------

verifyCase = (k, n, d, issue) -> (
    N := k * (n - k);
    print "=========================================";
    print("Case (k, n, d) = (" | toString k | ", " | toString n | ", " | toString d | "),  N = " | toString N);

    pluckerIdeal := Grassmannian(k - 1, n - 1, CoefficientRing => K);
    R := ring pluckerIdeal;
    use R;
    gensR := gens R;
    numGens := #gensR;

    -- Anti-symmetrize p_(i_1, ..., i_k)
    for inds in multiSubsets(n, k) do (
        if hasDuplicates inds then
            for perm in permutations inds do
                p_(toSequence perm) = 0
        else
            for perm in permutations inds do
                p_(toSequence perm) = (-1)^(countInversions perm) * p_(toSequence inds);
    );

    -- E_{ij} action helpers
    getIndex := mon -> (baseName mon)#1;
    exponentToMonomial := ls -> product (for i from 0 to numGens - 1 list (gensR#i)^(ls#i));

    differentiateMonomial := (i, j, mon) -> (
        exponent := sum (exponents mon)#0;
        ind := position((exponents mon)#0, lambda -> lambda == exponent);
        ls := getIndex(gensR#ind);
        if not member(j, ls) then return 0;
        if i != j and member(i, ls) then return 0;
        exponent * p_(replace(position(ls, lambda -> lambda == j), i, ls)) * p_ls^(exponent - 1)
    );

    differentiatePolynomial := (i, j, polynomial) -> (
        ans := 0;
        for monomial in terms polynomial do (
            expL := ((listForm monomial)#0)#0;
            coeff := ((listForm monomial)#0)#1;
            for lsIdx from 0 to numGens - 1 do (
                if expL#lsIdx > 0 then (
                    mon := (gensR#lsIdx)^(expL#lsIdx);
                    rest := new MutableList from expL;
                    rest#lsIdx = 0;
                    ans = ans + coeff * differentiateMonomial(i, j, mon) * exponentToMonomial(toList rest);
                );
            );
        );
        ans
    );

    buildJacobian := f -> (
        Iloc := ideal flatten (
            flatten for i from 0 to n - 2 list
                differentiatePolynomial(i, i, f) - differentiatePolynomial(i + 1, i + 1, f),
            flatten flatten for i from 0 to n - 1 list
                for j from i + 1 to n - 1 list {
                    differentiatePolynomial(i, j, f),
                    differentiatePolynomial(j, i, f)
                }
        );
        Iloc + ideal f
    );

    -- Try up to MAX_ATTEMPTS times to get a smooth f
    local f; local I;
    f := randomIntPoly(d, R);
    I := buildJacobian f;


    J := R / (I + pluckerIdeal);
    griffRing := for p from 1 to N list hilbertFunction(p * d - n, J);

    -- Expected primitive Hodge numbers via Schubert2
    G := flagBundle {k, n - k};
    Z := sectionZeroLocus OO_G(d);
    OmG := cotangentBundle G;
    OmZ := cotangentBundle Z;
    dimZ := dim Z;

    halfDimZ := floor(dimZ / 2);
    primHalf := for i from 0 to halfDimZ list
        abs(chi exteriorPower(i, OmZ) - chi exteriorPower(i, OmG));
    primFull := if dimZ % 2 == 0 then
        join(primHalf, reverse drop(primHalf, -1))
    else
        join(primHalf, reverse primHalf);

    -- Side-by-side comparison
    -- print "  p | (R/J_f)_{pd-n} | h^{N-p,p-1}_prim(Z) | match?";
    -- for p from 1 to N do (
    --     gr := griffRing#(p - 1);
    --     idx := N - p;
    --     hd := if idx >= 0 and idx < #primFull then primFull#idx else 0;
    --     m := if gr == hd then "OK" else "DIFF (delta = " | toString (gr - hd) | ")";
    --     print("  " | toString p | " | " | toString gr | " | " | toString hd | " | " | m);
    -- );

    -- Ready-to-paste LaTeX rows
    print "";
    print "  -- LaTeX (primitive cohomology row):";
    print("    " | makePrimRow(k, n, d, primFull, N));
    print "  -- LaTeX (Griffiths ring row):";
    print("    " | makeGriffRow(k, n, d, griffRing, issue, N));
    print "";
);

-- Test cases (all rows from the non-examples table) ---------------------

testCases = {
    -- d = 1
    (2, 5, 1, "$k=2,\\,2d|(n+1)$"),
    (3, 6, 1, "$d|n|2kd$"),
    (4, 8, 1, "$d|n|kd$"),
    (3, 9, 1, "$d|n|3kd$"),
    -- d = 2
    (2, 4, 2, "$d|n|kd$"),
    (3, 6, 2, "$d|n|kd$"),
    (2, 7, 2, "$k=2,\\,2d|(n+1)$"),

    -- d = 3
    (3, 4, 3, "$k = n-1$"),

     -- these are SLOW, consider commenting out
    (2, 5, 3, "$k=2,\\,2d|(n+1)$"),
    (2, 6, 3, "$d|n|kd$"),
    -- d >= 4
    (5, 6, 5, "$k = n-1$")
};

for case in testCases do (
    k := case#0;
    n := case#1;
    d := case#2;
    issue := case#3;
    verifyCase(k, n, d, issue);
);

print "All cases done.";