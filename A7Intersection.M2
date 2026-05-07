needsPackage "Cyclotomic";

K = toField(QQ[t]/(t^2 + t + 2));
b = K_0;
B = -1 - b;

r = matrix(K, {{0,1,0,0,0,0,0,0,0,0},{0,0,0,1,0,0,0,0,0,0},{0,0,0,0,0,1,0,0,0,0},{1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,1,0},{1,-1/2*B,-b-1/2*B,1/2*B,0,1/2*b-1/4*B,-1/2*B,-1/2*b-1/4*B,-1/2*B,-b-1/2*B},{1,-1/2*B,-1/2*B,-b-1/2*B,1,3/2*b+3/4*B,-1/2*B,1/2*b+3/4*B,-1/2*B,-b-1/2*B},{0,B,0,b,-1,1,-1,-B,-b,b},{-2*b-B,b+3/2*B,b+3/2*B,b-1/2*B,-B,-1/2*b-3/4*B,-b-1/2*B,-1/2*b+1/4*B,-b-1/2*B,1/2*B},{-b+1/2*B,1/2*b-1/4*B,-1/2*b-3/4*B,-3/2*b-1/4*B,-2*b-3/2*B,3/4*b-3/8*B,-3/2*b-5*B/4,3/4*b+13*B/8,-1/2*b-3/4*B,-1/2*b+5/4*B}});

s = matrix(K, {{0,0,1,0,0,0,0,0,0,0},{0,0,0,0,1,0,0,0,0,0},{0,0,0,0,0,0,1,0,0,0},{0,0,0,0,0,0,0,1,0,0},{0,0,0,0,0,0,0,0,0,1},{-b-1/2*B,1/2*b+1/4*B,1/2*b+1/4*B,-1/2*b-3/4*B,-1/2*B,1/4*b-1/8*B,-1/2*b-3/4*B,-3/4*b-1/8*B,1/2*b+1/4*B,-1/2*b-1/4*B},{1,-1/2*B,-b-1/2*B,1/2*B,0,1/2*b-1/4*B,-1/2*B,-1/2*b-1/4*B,-1/2*B,-b-1/2*B},{b+1/2*B,1/2*b+3/4*B,1/2*b+3/4*B,1/2*b-1/4*B,b+1/2*B,-1/4*b+5/8*B,1/2*b-1/4*B,-5/4*b-11/8*B,1/2*b+3/4*B,-1/2*b-3/4*B},{-2,-B,0,-b,0,0,0,0,0,0},{B,2,B,b+2*B,-b,-b-2*B,-b,-2,1,b+2*B}});

n = 10;
triples = flatten flatten for i from 0 to n-1 list
            for j from i+1 to n-1 list
              for l from j+1 to n-1 list {{i,j,l}};
m = #triples;

det3 = (A, R, C) -> (        -- fixed: 0-indexed
  r1 := R#0; r2 := R#1; r3 := R#2;
  c1 := C#0; c2 := C#1; c3 := C#2;
  a11 := A_(r1,c1); a12 := A_(r1,c2); a13 := A_(r1,c3);
  a21 := A_(r2,c1); a22 := A_(r2,c2); a23 := A_(r2,c3);
  a31 := A_(r3,c1); a32 := A_(r3,c2); a33 := A_(r3,c3);
  a11*(a22*a33-a23*a32) - a12*(a21*a33-a23*a31) + a13*(a21*a32-a22*a31)
);


wr = exteriorPower(3,r);
ws = exteriorPower(3,s);
-- I  = id_(K^m);

Aeq  = (wr - 1) || (ws - 1);   -- fixed: || not **
Wgen = mingens ker Aeq;

print("Invariant subspace dimension: " | toString numgens source Wgen);
print Wgen;
fCoeffs = flatten entries Wgen_{0};