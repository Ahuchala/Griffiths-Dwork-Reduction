needsPackage "WeilDivisors";
allowableThreads = 8;

n = 6;
k = 2;

K = QQ;

d = 2;

pluckerIdeal = Grassmannian(k-1,n-1,CoefficientRing=>K);
R = ring pluckerIdeal;



f=-44*p_(0,1)^2-43*p_(0,2)^2+29*p_(1,2)^2+27*p_(0,3)^2+13*p_(1,3)^2+5*p_(2,3)^2-15*p_(0,4)^2-41*p_(1,4)^2-25*p_(2,4)^2-43*p_(3,4)^2-10*p_(0,5)^2+6*p_(1,5)^2+35*p_(2,5)^2-8*p_(3,5)^2-19*p_(4,5)^2

isSmooth(pluckerIdeal+ideal f,IsGraded=>true)

