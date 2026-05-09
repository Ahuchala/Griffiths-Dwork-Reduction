-- hodge.m2
--
-- Self-contained Macaulay2 calculators mirroring the BWB-based algorithms
-- on https://andyhuchala.com/hodge.  No external packages required.
--
-- Provides:
--   chiGr(k, n, j, t)             -- chi(Omega^j_{Gr(k,n)}(t))           [QQ]
--   chiCI(k, n, degrees, t)       -- {chi(Omega^j_Z(t)) : j = 0..dim Z}  [QQ list]
--   chiPnCI(n, degrees, t)        -- same for CI in P^n
--   hodgeDiamondCI(k, n, degs)    -- full Hodge diamond of CI in Gr(k,n)
--   hodgeDiamondPnCI(n, degs)     -- full Hodge diamond of CI in P^n
--   twistedHodgeGr(k, n, t)       -- {(p, q, dim, lambda)} entries of h^{p,q}(Gr, O(t))
--                                    aggregated as: twistedHodgeNumbers(k, n, t)
--   prettyDiamond D               -- pretty-print a diamond as rows of length 2N+1
--
-- Run with:  M2 hodge.m2
-- Example:   hodgeDiamondPnCI(4, {3, 2})           -- quintic threefold X_{3,2} ⊂ P^4
--            twistedHodgeNumbers(2, 5, 3)          -- h^{p,q}(Gr(2,5), O(3))

-- ===========================================================
-- Partitions
-- ===========================================================

-- Partitions λ_1 >= ... >= λ_l > 0 with l <= k, λ_1 <= m, |λ| = target.
partitionsInBox = (k, m, target) -> (
    if target < 0 or k < 0 or m < 0 then return {};
    if target == 0 then return {{}};
    if k == 0 then return {};
    flatten for v in reverse toList(1..min(m, target)) list (
        for tail in partitionsInBox(k - 1, v, target - v) list prepend(v, tail)
    )
)

-- All partitions with parts <= maxPart and length <= maxLen (any size).
boundedPartitions = (maxPart, maxLen) -> (
    if maxLen <= 0 or maxPart <= 0 then return {{}};
    {{}} | flatten for v from 1 to maxPart list (
        for tail in boundedPartitions(v, maxLen - 1) list prepend(v, tail)
    )
)

-- Conjugate (transpose) partition padded to length m.
conjugatePart = (lambda, m) -> (
    t := new MutableList from toList(m : 0);
    for a from 0 to #lambda - 1 do
        for b from 0 to lambda#a - 1 do
            t#b = t#b + 1;
    toList t
)

-- Transpose of a partition (no padding).
transposePart = lambda -> (
    if #lambda == 0 then return {};
    w := max lambda;
    for j from 0 to w - 1 list #select(lambda, x -> x > j)
)

-- Hook length h_λ(a,b) at 1-indexed cell (a,b).
hookLength = (lambda, lambdaT, a, b) -> (
    la := if a <= #lambda then lambda#(a - 1) else 0;
    lb := if b <= #lambdaT then lambdaT#(b - 1) else 0;
    la + lb - a - b + 1
)

-- ===========================================================
-- Bott on Gr(k,n):  chi(Omega^j(t))
-- ===========================================================
-- f_λ(t) = ∏_{(a,b) ∈ k×m} (h_λ(a,b) - t) / h_λ(a,b).
-- chi(Omega^j_{Gr(k,n)}(t)) = (-1)^j Σ_{|λ|=j, λ⊆k×m} f_λ(t).

fLambda = (lambda, k, m, t) -> (
    lT := conjugatePart(lambda, m);
    num := 1;
    den := 1;
    zeroFactor := false;
    for a from 1 to k do
        for b from 1 to m do (
            h := hookLength(lambda, lT, a, b);
            if h == 0 then (
                if t != 0 then zeroFactor = true
                -- h == 0 and t == 0: factor (h-t)/h = 0/0; L'Hôpital → 1, skip.
            )
            else (
                num = num * (h - t);
                den = den * h;
            );
        );
    if zeroFactor then 0/1 else num/den
)

chiGr = (k, n, j, t) -> (
    m := n - k;
    if j < 0 or j > k * m then return 0/1;
    s := sum for lambda in partitionsInBox(k, m, j) list fLambda(lambda, k, m, t);
    if s === 0 then s = 0/1;
    (if even j then 1 else -1) * s
)

-- ===========================================================
-- CI recurrence (Koszul + conormal)
-- ===========================================================
-- chi(Omega^j_{Z_s}(t)) = chi(Omega^j_{Z_{s-1}}(t))
--                       - chi(Omega^j_{Z_{s-1}}(t - d_s))
--                       - chi(Omega^{j-1}_{Z_s}(t - d_s))

buildChiCI = (k, n, degrees) -> (
    cache := new MutableHashTable;
    chi := null;
    chi = (s, j, t) -> (
        if j < 0 then return 0/1;
        key := (s, j, t);
        if cache#?key then return cache#key;
        val := if s == 0 then chiGr(k, n, j, t)
            else (
                d := degrees#(s - 1);
                chi(s - 1, j, t) - chi(s - 1, j, t - d) - chi(s, j - 1, t - d)
            );
        cache#key = val;
        val
    );
    chi
)

chiCI = method()
chiCI(ZZ, ZZ, List, ZZ) := (k, n, degrees, t) -> (
    dimZ := k * (n - k) - #degrees;
    if dimZ < 0 then error "dim Z < 0";
    chi := buildChiCI(k, n, degrees);
    r := #degrees;
    for j from 0 to dimZ list chi(r, j, t)
)
chiCI(ZZ, ZZ, List) := (k, n, degrees) -> chiCI(k, n, degrees, 0)

chiPnCI = method()
chiPnCI(ZZ, List, ZZ) := (n, degrees, t) -> chiCI(1, n + 1, degrees, t)
chiPnCI(ZZ, List)     := (n, degrees) -> chiCI(1, n + 1, degrees, 0)

-- ===========================================================
-- Hodge diamond of a CI
-- ===========================================================
-- Lefschetz: h^{p,q}(Z) = h^{p,q}(Gr) for p+q != dim Z.
-- On Gr(k,n), h^{p,p} = #{partitions in k×m of size p}, all off-diagonal 0.
-- Middle row primitive part (j = 0 .. floor(dim/2)):
--   h^{dim-j, j}_prim = (-1)^{dim-j} (chi(Omega^j_Z(0)) - (-1)^j a_j),
-- where a_j = h^{j,j}(Gr).

hodgePrimitiveMiddleRow = (k, n, degrees) -> (
    m := n - k;
    dimZ := k*m - #degrees;
    if dimZ < 0 then error "dim Z < 0";
    chi := buildChiCI(k, n, degrees);
    r := #degrees;
    half := dimZ // 2;
    for j from 0 to half list (
        chiVal := chi(r, j, 0);
        a := #partitionsInBox(k, m, j);
        sign := if even (dimZ - j) then 1 else -1;
        chiSign := if even j then 1 else -1;
        lift(sign * (chiVal - chiSign * a), ZZ)
    )
)

-- Returns a list of (2 dim + 1) antidiagonal rows; row i has min(i+1, 2*dim+1-i)
-- entries.  With PrettyPrint => true (the default) the diamond is printed and
-- nothing is returned; pass PrettyPrint => false to get the raw nested list.
hodgeDiamondCI = method(Options => {PrettyPrint => true})
hodgeDiamondCI(ZZ, ZZ, List) := o -> (k, n, degrees) -> (
    m := n - k;
    dimZ := k*m - #degrees;
    if dimZ < 0 then error "dim Z < 0";
    a := for j from 0 to dimZ list #partitionsInBox(k, m, j);
    prim := hodgePrimitiveMiddleRow(k, n, degrees);
    half := dimZ // 2;
    isOdd := odd dimZ;
    midHalf := for j from 0 to half list (
        prim#j + (if (not isOdd) and j == half then a#half else 0)
    );
    midFull := if isOdd then midHalf | reverse midHalf
               else midHalf | reverse drop(midHalf, -1);
    D := for i from 0 to 2*dimZ list (
        rowSize := if i <= dimZ then i + 1 else 2*dimZ - i + 1;
        if i == dimZ then midFull
        else (
            mirrorI := if i < dimZ then i else 2*dimZ - i;
            if even mirrorI then (
                colJ := mirrorI // 2;
                for j from 0 to rowSize - 1 list (if j == colJ then a#colJ else 0)
            )
            else toList(rowSize : 0)
        )
    );
    if o.PrettyPrint then (prettyDiamond D; null) else D
)

hodgeDiamondPnCI = method(Options => {PrettyPrint => true})
hodgeDiamondPnCI(ZZ, List) := o -> (n, degrees) ->
    hodgeDiamondCI(1, n + 1, degrees, PrettyPrint => o.PrettyPrint)

-- ===========================================================
-- Twisted Hodge numbers h^q(Gr(k,n), Omega^p(t)) via Bott
-- ===========================================================
-- Mirrors components/hodge/twistedHodge.js: enumerate partitions, regularize
-- α = (−rev(λᵀ), λ−t) by sorting α + ρ, and pick up Schur dim contributions.

-- Schur (Weyl) dimension for highest weight beta of GL_n.
schurDim = beta -> (
    n := #beta;
    num := 1;
    den := 1;
    for a from 0 to n - 1 do
        for b from a + 1 to n - 1 do (
            num = num * (beta#a - beta#b + (b - a));
            den = den * (b - a);
        );
    num // den
)

-- t-skew μ ↦ λ.
tSkew = (mu, t) -> (
    n := #mu;
    if n == 0 then return {};
    l := new MutableList from toList(n : 0);
    for ii from 0 to n - 1 do (
        i := n - 1 - ii;
        j := i + t - mu#i;
        l#i = if j < n then mu#i + l#j else mu#i;
    );
    L := toList l;
    while #L > 0 and last L == 0 do L = drop(L, -1);
    L
)

-- Returns a list of tuples (p, q, dimension, lambda) for nonzero contributions.
twistedHodgeGr = (k, n, t) -> (
    nMinusK := n - k;
    N := k * nMinusK;

    if t < 0 then (
        pos := twistedHodgeGr(k, n, -t);
        return for x in pos list (N - x#0, N - x#1, x#2, x#3);
    );

    if t == 0 then (
        -- chi-trick: at t = 0 only the diagonal h^{p,p} survives, equal to
        -- the q-binomial coefficient = #{partitions in k×(n-k) of size p}.
        return for p from 0 to N list (p, p, #partitionsInBox(k, nMinusK, p), {});
    );

    shift := for i from 0 to n - 1 list n - i;       -- (n, n-1, ..., 1)
    rho   := for i from 0 to n - 1 list n - i - 1;   -- (n-1, ..., 0)

    -- candidates are pairs (lambda, muSize); for t >= n every λ is a t-core
    -- and lives entirely in H^0 (q = 0), so we record muSize = |λ|.
    candidates := if t >= n then for lam in boundedPartitions(nMinusK, k) list (lam, sum lam)
        else (
            seen := new MutableHashTable;
            out := {};
            for mu in boundedPartitions(t - 1, k) do (
                lam := tSkew(mu, t);
                key := (lam, sum mu);
                if not seen#?key then (
                    seen#key = true;
                    out = append(out, (lam, sum mu));
                );
            );
            out
        );

    results := {};
    for cand in candidates do (
        (lambda, muSize) := cand;
        if #lambda > k then continue;
        if #lambda > 0 and max lambda > nMinusK then continue;

        lamT := reverse transposePart lambda;
        alpha := new MutableList from toList(n : 0);
        startL := nMinusK - #lamT;
        for i from 0 to #lamT - 1 do alpha#(startL + i) = - lamT#i;
        for i from 0 to k - 1 do (
            v := if i < #lambda then lambda#i else 0;
            alpha#(nMinusK + i) = v - t;
        );

        -- Regularity: α + shift must have distinct entries.
        shifted := for i from 0 to n - 1 list alpha#i + shift#i;
        if # set shifted != n then continue;

        -- Sort α + ρ in decreasing order; subtract ρ to get dominant β.
        aPlusRho := reverse sort(for i from 0 to n - 1 list alpha#i + rho#i);
        beta := for i from 0 to n - 1 list aPlusRho#i - rho#i;

        p := sum lambda;
        q := p - muSize;
        results = append(results, (p, q, schurDim beta, lambda));
    );
    results
)

-- Aggregate twistedHodgeGr into a Hodge-diamond shape:
-- a list of 2N+1 antidiagonal rows, row r = (p+q) holding entries h^{p,r-p}
-- for p = max(0, r-N) .. min(r, N).
twistedHodgeNumbers = method(Options => {PrettyPrint => true})
twistedHodgeNumbers(ZZ, ZZ, ZZ) := o -> (k, n, t) -> (
    N := k * (n - k);
    M := new MutableHashTable;
    for tup in twistedHodgeGr(k, n, t) do (
        (p, q, d, lam) := tup;
        key := (p, q);
        M#key = (if M#?key then M#key else 0) + d;
    );
    -- r = 2N at top (h^{N,N}); within each row, p decreases left-to-right
    -- so the leftmost entry is h^{p_max, q_min} (standard convention).
    D := for r in reverse toList(0 .. 2*N) list (
        for q from max(0, r - N) to min(r, N) list (
            key := (r - q, q);
            if M#?key then M#key else 0
        )
    );
    if o.PrettyPrint then (prettyDiamond D; null) else D
)

-- ===========================================================
-- Pretty-printing
-- ===========================================================

prettyDiamond = D -> (
    rows := #D;
    width := max apply(D, r -> #r);
    cellW := 2 + max flatten apply(D, r -> apply(r, x -> #toString x));
    pad := s -> (
        s = toString s;
        concatenate(toList((cellW - #s) : " "), s)
    );
    for row in D do (
        leading := (width - #row) * cellW // 2;
        << concatenate(toList(leading : " "));
        for x in row do << pad x;
        << endl;
    );
)

-- ===========================================================
-- Examples (uncomment to run on load)
-- ===========================================================

-- << "Quintic threefold X_5 in P^4:" << endl;
-- hodgeDiamondPnCI(4, {5});

-- << "Cubic fourfold X_3 in P^5:" << endl;
-- hodgeDiamondPnCI(5, {3});

-- << "(2,2,2) CI in Gr(2,5):" << endl;
-- hodgeDiamondCI(2, 5, {2,2,2});

-- << "h^{p,q}(Gr(2,5), O(3)):" << endl;
-- twistedHodgeNumbers(2, 5, 3);

-- -- Get the raw nested list instead of pretty-printing:
-- hodgeDiamondPnCI(4, {5}, PrettyPrint => false)
