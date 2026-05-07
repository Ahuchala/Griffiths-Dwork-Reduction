K = QQ;


r = matrix(K, {
    {-1, 2, 0, 1, 0,-1, 2,-1, 1,-1},
    {-1, 1, 1, 0, 0,-1, 1,-1, 0, 0},
    { 0, 1, 0, 0,-1,-1, 0, 0, 0,-1},
    { 0, 0, 1, 0, 1,-1, 0,-1, 1, 1},
    {-1, 0, 1, 0, 0,-1, 0, 0, 0, 1},
    { 0, 1, 0, 0,-1,-1, 1,-1, 0,-1},
    { 0, 1,-1, 1,-1, 0, 1, 0, 0,-1},
    { 0, 0, 0, 1, 0, 0, 0, 0, 0, 0},
    { 1,-1,-1, 0, 0, 1,-1, 0, 0,-1},
    { 0, 0, 0, 0, 0, 1, 0, 0, 0, 0}});

s = matrix(K, {
    {-1, 2, 1, 0, 0,-2, 2,-1, 1, 0},
    { 0, 1, 0, 0,-1,-1, 1,-1, 0,-1},
    { 0, 1, 0, 0, 0, 0, 0, 0, 0, 0},
    { 1,-1,-1,-1, 0, 1,-2, 1, 0, 0},
    { 0, 0, 0, 0, 0,-1, 0,-1, 0, 0},
    { 0, 0, 0, 0, 0, 1, 0, 0, 0, 0},
    {-1, 1, 1, 1, 1,-1, 2,-1, 1, 1},
    {-1, 2, 0, 1, 0,-2, 2,-1, 1, 0},
    {-1, 1, 0, 0,-1, 0, 0, 1, 0, 0},
    { 0, 0, 0, 0, 0, 0, 1, 0, 0, 0}});
n = 10;
triples = flatten flatten for i from 0 to n-1 list
            for j from i+1 to n-1 list
              for l from j+1 to n-1 list {{i,j,l}};

wr = exteriorPower(3,r);
ws = exteriorPower(3,s);
-- I  = id_(K^m);

Aeq  = (wr - 1) || (ws - 1);   -- fixed: || not **
Wgen = mingens ker Aeq;

print("Invariant subspace dimension: " | toString numgens source Wgen);
-- print Wgen;
fCoeffs = -1 * flatten entries Wgen_{0}