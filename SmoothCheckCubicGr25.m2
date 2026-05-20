-- SmoothCheckCubicGr25.m2
--
-- Confirms that the cubic Z = V(f) in Gr(2, 5) used by
-- GriffithsRingCubicGr25.m2 is smooth, via isSmooth(I + (f)) on the
-- Plucker ideal plus (f) with IsGraded=>true.
--
-- Run with:  M2 SmoothCheckCubicGr25.m2

needsPackage "WeilDivisors";
allowableThreads = 8;

n = 5;
k = 2;

K = QQ;

d = 3;

pluckerIdeal = Grassmannian(k-1,n-1,CoefficientRing=>K);
R = ring pluckerIdeal;



f=-9*p_(0,1)^3-34*p_(0,2)^3-47*p_(1,2)^3+25*p_(0,3)^3-37*p_(1,3)^3+50*p_(2,3)^3-9*p_(0,4)^3+12*p_(1,4)^3+16*p_(2,4)^3-36*p_(3,4)^3

isSmooth(pluckerIdeal+ideal f,IsGraded=>true)

