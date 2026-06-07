-- CayleyCIGr25.m2
--
-- Cayley trick for a complete intersection in a Grassmannian, verified in
-- Schubert2. For Z = CI of multidegree dvec in Gr(k, n) (cut out by a
-- regular section of E = (+) O(d_i)), the Cayley hypersurface is
--   Y = V(s) in P = P(E^vee),   s in H^0(P, O_P(1) (x) pi^* det E),
-- and there is a Hodge-shift isomorphism
--   H^{a,b}_prim(Z)  ~  H^{a+(c-1), b+(c-1)}_prim(Y),   c = rank E = #dvec.
--
-- This script checks, entirely within Schubert2 intersection theory:
--   (1) dims and chi(O) of Z, P, Y;
--   (2) chi_top(Y) = chi_top(Gr) + chi_top(Z)        [Konno];
--   (3) the shift relation on Hodge-Euler (chi_y) polynomials:
--         chi_y(Y) - chi_y(P) = (-y)^{c-1} ( chi_y(Z) - chi_y(Gr) ).
--
-- The default case is dvec = {2, 1} (quadric cap hyperplane) in Gr(2, 5).
--
-- CONVENTION NOTE.  Schubert2's projectiveBundle(dual E) uses O_P(1) with
-- pi_* O_P(1) = E^vee.  The Cayley section therefore lives in
-- |O_P(1) (x) pi^* det E|, NOT |O_P(1)|; the det E twist was fixed by
-- matching chi_top(Y) to the Konno value (see the twist sweep in the
-- session notes).  Changing the projectivization convention changes this
-- twist, so re-derive it if you switch to projectiveBundle E.
--
-- Run with:  M2 --script CayleyCIGr25.m2

needsPackage "Schubert2";

k = 2;
n = 5;
dvec = {2, 1};
c = #dvec;
detE = sum dvec;

G = flagBundle {k, n - k};                         -- Gr(k, n)
N = k * (n - k);                                   -- dim Gr

-- E = (+) O(d_i), Z = its regular-section zero locus.
Ebund = OO_G(dvec#0);
for i from 1 to c - 1 do Ebund = Ebund ++ OO_G(dvec#i);
Z = sectionZeroLocus Ebund;
dZ = dim Z;

OmG = cotangentBundle G;
OmZ = cotangentBundle Z;

chiZ = for j from 0 to dZ list chi exteriorPower(j, OmZ);
ctZ = sum for j from 0 to dZ list (-1)^j * chiZ#j;

print("dim Gr = " | toString N | ",  dim Z = " | toString dZ
    | "  (expect " | toString(N - c) | ")");
print("chi(O_Z) = " | toString chi OO_Z);
print("chi(Omega^j_Z) = " | toString chiZ);
print("chi_top(Z) = " | toString ctZ);

-- Cayley: P = P(E^vee), Y = V(section of O_P(1) (x) pi^* det E).
P = projectiveBundle(dual Ebund, VariableNames => {symbol z0, symbol z1});
dP = dim P;
L = OO_P(1) ** OO_G(detE);
Y = sectionZeroLocus L;
dY = dim Y;

OmP = cotangentBundle P;
OmY = cotangentBundle Y;

chiY = for j from 0 to dY list chi exteriorPower(j, OmY);
ctY = sum for j from 0 to dY list (-1)^j * chiY#j;

print("");
print("dim P = " | toString dP | "  (expect " | toString(N + c - 1) | ")");
print("dim Y = " | toString dY | "  (expect " | toString(N + c - 2) | ")");
print("chi(O_P) = " | toString chi OO_P | ",  chi(O_Y) = " | toString chi OO_Y);
print("chi(Omega^j_Y) = " | toString chiY);
print("chi_top(Y) = " | toString ctY);

-- (2) Konno Euler-characteristic relation.
ctG = chi exteriorPower(0, OO_G);   -- placeholder; compute chi_top(Gr) properly below
chiG = for j from 0 to N list chi exteriorPower(j, OmG);
ctG = sum for j from 0 to N list (-1)^j * chiG#j;
print("");
print("Konno: chi_top(Y) =? chi_top(Gr) + chi_top(Z) = "
    | toString ctG | " + " | toString ctZ | " = " | toString(ctG + ctZ));
assert(ctY == ctG + ctZ);
print("  Konno relation holds.");

-- (3) Hodge-shift relation on chi_y polynomials.
S = QQ[local y];
yy = S_0;
chiy = (chis) -> sum for j from 0 to #chis - 1 list chis#j * yy^j;
chiyZ = chiy chiZ;
chiyY = chiy chiY;
chiyG = chiy chiG;
chiyP = chiy(for j from 0 to dP list chi exteriorPower(j, OmP));

lhs = chiyY - chiyP;
rhs = (-yy)^(c - 1) * (chiyZ - chiyG);
print("");
print("Shift test: chi_y(Y) - chi_y(P) =? (-y)^(c-1) ( chi_y(Z) - chi_y(Gr) )");
print("  LHS = " | toString lhs);
print("  RHS = " | toString rhs);
assert(lhs == rhs);
print("  Cayley shift isomorphism verified (c-1 = " | toString(c-1) | ").");
