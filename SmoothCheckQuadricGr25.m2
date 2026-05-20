-- SmoothCheckQuadricGr25.m2
--
-- Confirms that the quadric Z = V(f) in Gr(2, 5) used by
-- GriffithsRingQuadricGr25.m2 is smooth, via isSmooth on the Plucker
-- ideal plus (f) with IsGraded=>true.
--
-- Run with:  M2 SmoothCheckQuadricGr25.m2

needsPackage "WeilDivisors";
allowableThreads = 8;

n = 5;
k = 2;

K = QQ;

d = 2;

pluckerIdeal = Grassmannian(k-1,n-1,CoefficientRing=>K);
R = ring pluckerIdeal;



f=12*p_(0,1)^2+17*p_(0,2)^2+44*p_(1,2)^2+50*p_(0,3)^2+56*p_(1,3)^2+40*p_(2,3)^2+71*p_(0,4)^2+48*p_(1,4)^2+79*p_(2,4)^2+19*p_(3,4)^2

isSmooth(pluckerIdeal+ideal f,IsGraded=>true)

