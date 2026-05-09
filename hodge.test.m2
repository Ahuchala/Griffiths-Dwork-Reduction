-- hodge.test.m2
--
-- Tests for hodge.m2, ported from tests/hodge.test.js (the website's test suite).
-- Only tests that exercise functions defined in hodge.m2 are included:
--   * hodgeDiamondCI  (CI in Gr(k,n); equivalently in P^n via Gr(1, n+1))
--   * chiCI / chiGr
--   * hodgePrimitiveMiddleRow
--   * twistedHodgeGr
--
-- Run with:  M2 hodge.test.m2

load "hodge.m2"

-- ===========================================================
-- Tiny test harness
-- ===========================================================

passed = 0
failed = 0
failures = {}

-- Note: the name 'check' is reserved by M2's package-testing machinery.
assertEq = (name, expected, actual) -> (
    if expected === actual then passed = passed + 1
    else (
        failed = failed + 1;
        failures = append(failures, (name, expected, actual));
    );
)

-- Coerce a list of QQ values (each really an integer by Bott) to ZZ.
toInts = L -> apply(L, x -> if instance(x, QQ) then lift(x, ZZ) else x)

-- Aggregate twistedHodgeGr into a (p, q) -> dimension HashTable.
twistedMap = (k, n, t) -> (
    M := new MutableHashTable;
    for tup in twistedHodgeGr(k, n, t) do (
        (p, q, d, lam) := tup;
        key := (p, q);
        M#key = (if M#?key then M#key else 0) + d;
    );
    M
)

diamond = (k, n, d) -> hodgeDiamondCI(k, n, d, PrettyPrint => false)

-- ===========================================================
-- CI in P^n (= Gr(1, n+1))
-- ===========================================================

-- Plane curves: genus g = (d-1)(d-2)/2, middle row = {g, g}
assertEq("CI: conic in P^2 (P^1, g=0)",            {0, 0}, (diamond(1, 3, {2}))#1)
assertEq("CI: cubic in P^2 (elliptic, g=1)",       {1, 1}, (diamond(1, 3, {3}))#1)
assertEq("CI: quartic in P^2 (g=3)",               {3, 3}, (diamond(1, 3, {4}))#1)
assertEq("CI: quintic in P^2 (g=6)",               {6, 6}, (diamond(1, 3, {5}))#1)
assertEq("CI: sextic in P^2 (g=10)",             {10, 10}, (diamond(1, 3, {6}))#1)

-- Surfaces in P^3 (dim = 2)
assertEq("CI: quadric in P^3 (h^{1,1}=2)",        {0, 2, 0}, (diamond(1, 4, {2}))#2)
assertEq("CI: cubic surface in P^3 (h^{1,1}=7)",  {0, 7, 0}, (diamond(1, 4, {3}))#2)
assertEq("CI: quartic K3 (h^{1,1}=20)",          {1, 20, 1}, (diamond(1, 4, {4}))#2)
assertEq("CI: hyperplane in P^3 (= P^2)",         {0, 1, 0}, (diamond(1, 4, {1}))#2)

-- CI of higher codimension in P^n
assertEq("CI: 2 quadrics in P^3 (elliptic)",         {1, 1}, (diamond(1, 4, {2,2}))#1)
assertEq("CI: quadric+cubic in P^3 (g=4)",           {4, 4}, (diamond(1, 4, {2,3}))#1)
assertEq("CI: 2 quadrics in P^4 (h^{1,1}=6)",     {0, 6, 0}, (diamond(1, 5, {2,2}))#2)
assertEq("CI: quadric+cubic in P^4 (K3)",        {1, 20, 1}, (diamond(1, 5, {2,3}))#2)
assertEq("CI: 3 quadrics in P^5 (K3)",           {1, 20, 1}, (diamond(1, 6, {2,2,2}))#2)

-- CY3: quintic threefold
assertEq("CI: quintic CY3 in P^4 (h^{2,1}=101)",
    {1, 101, 101, 1}, (diamond(1, 5, {5}))#3)

-- ===========================================================
-- chiCI: Euler characteristics in Gr(k,n)
-- ===========================================================

assertEq("chiCI Gr(2,5) d={2}: documented example",
    {1, -1, -8, 8, 1, -1}, toInts chiCI(2, 5, {2}))

assertEq("chiCI Gr(2,4) d={}: q-binom [4 choose 2]_q = (1,1,2,1,1)",
    {1, -1, 2, -1, 1}, toInts chiCI(2, 4, {}))

assertEq("chiCI Gr(2,5) d={}: q-binom [5 choose 2]_q",
    {1, -1, 2, -2, 2, -1, 1}, toInts chiCI(2, 5, {}))

assertEq("chiCI Gr(2,4) d={1}: hyperplane section, dim=3",
    {1, -1, 1, -1}, toInts chiCI(2, 4, {1}))

-- Serre duality: dim odd => chi(Omega^j) + chi(Omega^{dim-j}) = 0
serreDualityOdd = (k, n, degs) -> (
    chi := chiCI(k, n, degs);
    d := #chi - 1;
    all(0..d, j -> chi#j + chi#(d - j) === 0/1)
)
assertEq("chiCI Gr(2,5) d={2}: Serre duality (dim=5 odd)",
    true, serreDualityOdd(2, 5, {2}))

assertEq("chiCI Gr(2,8) d={1,1,1,1}: 4 hyperplanes, dim=8",
    {1, -1, 2, -3, 22, -3, 2, -1, 1}, toInts chiCI(2, 8, {1,1,1,1}))

-- Serre duality: dim even => chi(Omega^j) = chi(Omega^{dim-j})
assertEq("chiCI Gr(2,8) d={1,1,1,1}: Serre duality (dim=8 even)",
    true, all(0..8, j -> (chiCI(2, 8, {1,1,1,1}))#j === (chiCI(2, 8, {1,1,1,1}))#(8 - j)))

assertEq("chiCI Gr(2,7) d={1*7}: CY3, h^{2,1}=50",
    {0, 49, -49, 0}, toInts chiCI(2, 7, {1,1,1,1,1,1,1}))

-- ===========================================================
-- hodgeDiamondCI: full diamonds in Gr(k,n)
-- ===========================================================

assertEq("hodgeDiamondCI Gr(2,5) d={2}: full diamond",
    {{1}, {0,0}, {0,1,0}, {0,0,0,0}, {0,0,2,0,0}, {0,0,10,10,0,0},
     {0,0,2,0,0}, {0,0,0,0}, {0,1,0}, {0,0}, {1}},
    diamond(2, 5, {2}))

assertEq("hodgeDiamondCI Gr(2,7) d={1*7}: CY3 full diamond",
    {{1}, {0,0}, {0,1,0}, {1,50,50,1}, {0,1,0}, {0,0}, {1}},
    diamond(2, 7, {1,1,1,1,1,1,1}))

assertEq("hodgeDiamondCI Gr(2,8) d={1*4}: dim=8, h^{4,4}=22",
    {{1}, {0,0}, {0,1,0}, {0,0,0,0}, {0,0,2,0,0}, {0,0,0,0,0,0},
     {0,0,0,2,0,0,0}, {0,0,0,0,0,0,0,0}, {0,0,0,1,22,1,0,0,0},
     {0,0,0,0,0,0,0,0}, {0,0,0,2,0,0,0}, {0,0,0,0,0,0}, {0,0,2,0,0},
     {0,0,0,0}, {0,1,0}, {0,0}, {1}},
    diamond(2, 8, {1,1,1,1}))

-- ===========================================================
-- hodgePrimitiveMiddleRow: regression tests against the website JSON
-- ===========================================================

prim = hodgePrimitiveMiddleRow

assertEq("prim Gr(2,4) 1xd=2", {0, 2}, prim(2, 4, {2}))
assertEq("prim Gr(2,4) 2xd=2", {1, 19}, prim(2, 4, {2,2}))
assertEq("prim Gr(2,4) 3xd=2", {17}, prim(2, 4, {2,2,2}))
assertEq("prim Gr(2,5) 1xd=2", {0, 0, 10}, prim(2, 5, {2}))
assertEq("prim Gr(2,5) 2xd=2", {0, 20, 130}, prim(2, 5, {2,2}))
assertEq("prim Gr(2,5) 3xd=2", {10, 260}, prim(2, 5, {2,2,2}))
assertEq("prim Gr(2,5) 4xd=2", {135, 639}, prim(2, 5, {2,2,2,2}))
assertEq("prim Gr(2,5) 5xd=2", {401}, prim(2, 5, {2,2,2,2,2}))
assertEq("prim Gr(2,6) 1xd=2", {0, 0, 1, 69}, prim(2, 6, {2}))
assertEq("prim Gr(2,6) 2xd=2", {0, 2, 239, 956}, prim(2, 6, {2,2}))
assertEq("prim Gr(2,6) 3xd=2", {1, 271, 2972}, prim(2, 6, {2,2,2}))
assertEq("prim Gr(2,6) 4xd=2", {101, 3335, 9858}, prim(2, 6, {2,2,2,2}))
assertEq("prim Gr(2,6) 5xd=2", {1249, 11969}, prim(2, 6, {2,2,2,2,2}))
assertEq("prim Gr(2,7) 1xd=2", {0, 0, 0, 21, 441}, prim(2, 7, {2}))
assertEq("prim Gr(2,7) 2xd=2", {0, 0, 63, 2380, 7231}, prim(2, 7, {2,2}))
assertEq("prim Gr(2,7) 3xd=2", {0, 63, 4501, 31038}, prim(2, 7, {2,2,2}))
assertEq("prim Gr(2,7) 4xd=2", {21, 3633, 54824, 130122}, prim(2, 7, {2,2,2,2}))
assertEq("prim Gr(2,7) 5xd=2", {1071, 43239, 234718}, prim(2, 7, {2,2,2,2,2}))
assertEq("prim Gr(2,8) 1xd=2", {0, 0, 0, 1, 273, 3002}, prim(2, 8, {2}))
assertEq("prim Gr(2,8) 2xd=2", {0, 0, 3, 1148, 22219, 56295}, prim(2, 8, {2,2}))
assertEq("prim Gr(2,8) 3xd=2", {0, 3, 1809, 60507, 309210}, prim(2, 8, {2,2,2}))
assertEq("prim Gr(2,8) 4xd=2", {1, 1265, 78222, 756316, 1570297}, prim(2, 8, {2,2,2,2}))
assertEq("prim Gr(2,8) 5xd=2", {331, 48791, 931620, 3771648}, prim(2, 8, {2,2,2,2,2}))
assertEq("prim Gr(2,9) 1xd=2", {0, 0, 0, 0, 36, 2880, 20952}, prim(2, 9, {2}))
assertEq("prim Gr(2,9) 2xd=2", {0, 0, 0, 144, 16209, 200340, 446202}, prim(2, 9, {2,2}))
assertEq("prim Gr(2,10) 1xd=2", {0, 0, 0, 0, 1, 725, 27621, 150425}, prim(2, 10, {2}))
assertEq("prim Gr(2,10) 2xd=2", {0, 0, 0, 4, 3719, 198864, 1775059, 3588784}, prim(2, 10, {2,2}))
assertEq("prim Gr(2,11) 1xd=2", {0, 0, 0, 0, 0, 55, 11022, 251174, 1103641}, prim(2, 11, {2}))
assertEq("prim Gr(2,12) 1xd=2",
    {0, 0, 0, 0, 0, 1, 1572, 142286, 2215576, 8248019}, prim(2, 12, {2}))
assertEq("prim Gr(3,6) 1xd=2", {0, 0, 1, 140, 601}, prim(3, 6, {2}))
assertEq("prim Gr(3,6) 2xd=2", {0, 2, 449, 4524}, prim(3, 6, {2,2}))
assertEq("prim Gr(3,6) 3xd=2", {1, 481, 10532, 27881}, prim(3, 6, {2,2,2}))
assertEq("prim Gr(3,6) 4xd=2", {171, 9859, 62358}, prim(3, 6, {2,2,2,2}))
assertEq("prim Gr(3,6) 5xd=2", {3251, 58351, 142902}, prim(3, 6, {2,2,2,2,2}))
assertEq("prim Gr(3,7) 1xd=2", {0, 0, 0, 35, 2758, 20076}, prim(3, 7, {2}))
assertEq("prim Gr(3,7) 2xd=2", {0, 0, 105, 12215, 154672, 347542}, prim(3, 7, {2,2}))
assertEq("prim Gr(3,7) 3xd=2", {0, 105, 20097, 435792, 1864577}, prim(3, 7, {2,2,2}))
assertEq("prim Gr(3,7) 4xd=2",
    {35, 14581, 580104, 4534319, 8817808}, prim(3, 7, {2,2,2,2}))
assertEq("prim Gr(3,7) 5xd=2",
    {3941, 371161, 5592210, 20334007}, prim(3, 7, {2,2,2,2,2}))
assertEq("prim Gr(3,8) 1xd=2",
    {0, 0, 0, 1, 1112, 67305, 650553, 1351504}, prim(3, 8, {2}))
assertEq("prim Gr(4,8) 1xd=2",
    {0, 0, 0, 1, 1700, 155422, 2423049, 9017875}, prim(4, 8, {2}))

-- ===========================================================
-- Twisted Hodge h^{p,q}(Gr(k,n), O(t))
-- ===========================================================

-- P^1 = Gr(1,2)
M = twistedMap(1, 2, 1)
assertEq("twisted P^1, t=1: H^0(O(1)) = 2", 2, M#(0, 0))
assertEq("twisted P^1, t=1: 1 nonzero entry", 1, # keys M)

M = twistedMap(1, 2, 2)
assertEq("twisted P^1, t=2: H^0(O(2)) = 3", 3, M#(0, 0))
assertEq("twisted P^1, t=2: H^0(Omega^1(2)) = 1", 1, M#(1, 0))
assertEq("twisted P^1, t=2: 2 nonzero entries", 2, # keys M)

-- Serre duality on P^1: t=-1 mirrors t=1 at (N-p, N-q), N=1
M = twistedMap(1, 2, -1)
assertEq("twisted P^1, t=-1: Serre dual (h^{1,1}(O(-1)) = 0; h^1(K)=2)",
    2, M#(1, 1))
assertEq("twisted P^1, t=-1: 1 nonzero entry", 1, # keys M)

-- P^2 = Gr(1,3)
M = twistedMap(1, 3, 1)
assertEq("twisted P^2, t=1: H^0(O(1)) = 3", 3, M#(0, 0))
assertEq("twisted P^2, t=1: 1 nonzero entry", 1, # keys M)

M = twistedMap(1, 3, 2)
assertEq("twisted P^2, t=2: H^0(O(2)) = 6", 6, M#(0, 0))
assertEq("twisted P^2, t=2: H^0(Omega^1(2)) = 3", 3, M#(1, 0))
assertEq("twisted P^2, t=2: 2 nonzero entries", 2, # keys M)

M = twistedMap(1, 3, -1)
assertEq("twisted P^2, t=-1: Serre dual (h^{2,2}(O(-1)) = 3)", 3, M#(2, 2))
assertEq("twisted P^2, t=-1: 1 nonzero entry", 1, # keys M)

-- P^3 = Gr(1,4)
M = twistedMap(1, 4, 1)
assertEq("twisted P^3, t=1: H^0(O(1)) = 4", 4, M#(0, 0))

-- Gr(2,4) Plücker
M = twistedMap(2, 4, 1)
assertEq("twisted Gr(2,4), t=1: H^0(O(1)) = 6 (Plücker)", 6, M#(0, 0))
assertEq("twisted Gr(2,4), t=1: 1 nonzero entry", 1, # keys M)

M = twistedMap(2, 4, -1)
assertEq("twisted Gr(2,4), t=-1: Serre dual (h^{4,4}(O(-1)) = 6)", 6, M#(4, 4))

-- t=0: untwisted = ordinary Hodge diamond, diagonal only
M = twistedMap(2, 4, 0)
assertEq("twisted Gr(2,4), t=0: 5 diagonal entries", 5, # keys M)
assertEq("twisted Gr(2,4), t=0: h^{0,0}=1", 1, M#(0,0))
assertEq("twisted Gr(2,4), t=0: h^{1,1}=1", 1, M#(1,1))
assertEq("twisted Gr(2,4), t=0: h^{2,2}=2", 2, M#(2,2))
assertEq("twisted Gr(2,4), t=0: h^{3,3}=1", 1, M#(3,3))
assertEq("twisted Gr(2,4), t=0: h^{4,4}=1", 1, M#(4,4))

M = twistedMap(2, 5, 0)
assertEq("twisted Gr(2,5), t=0: 7 diagonal entries", 7, # keys M)
assertEq("twisted Gr(2,5), t=0: h^{0,0}=1", 1, M#(0,0))
assertEq("twisted Gr(2,5), t=0: h^{1,1}=1", 1, M#(1,1))
assertEq("twisted Gr(2,5), t=0: h^{2,2}=2", 2, M#(2,2))
assertEq("twisted Gr(2,5), t=0: h^{3,3}=2", 2, M#(3,3))
assertEq("twisted Gr(2,5), t=0: h^{4,4}=2", 2, M#(4,4))
assertEq("twisted Gr(2,5), t=0: h^{5,5}=1", 1, M#(5,5))
assertEq("twisted Gr(2,5), t=0: h^{6,6}=1", 1, M#(6,6))

-- Plücker embeddings (H^0(O(1)) = binom(n,k))
assertEq("twisted Gr(2,5), t=1: H^0(O(1)) = 10", 10, (twistedMap(2, 5, 1))#(0, 0))
assertEq("twisted Gr(3,6), t=1: H^0(O(1)) = 20", 20, (twistedMap(3, 6, 1))#(0, 0))

-- ===========================================================
-- Report
-- ===========================================================

<< endl;
<< "================================================================" << endl;
<< passed << " passed, " << failed << " failed" << endl;
if failed > 0 then (
    << "----------------------------------------------------------------" << endl;
    for f in failures do (
        << "FAIL: " << f#0 << endl;
        << "  expected: " << f#1 << endl;
        << "  actual:   " << f#2 << endl;
    );
    exit 1;
);
exit 0;
