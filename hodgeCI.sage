def Phi_Gr(k, n):
    """
    Phi_X(x, t) for X = Gr(k, n), as an element of Q[x, t].
    Uses the t-hook ratio formula directly.
    """
    m = n - k
    R = PolynomialRing(QQ, ['x', 't'])
    x, t = R.gens()

    def hook(la, a, b):
        # standard hook length of partition la at cell (a, b), 1-indexed
        return la[a-1] - b + sum(1 for u in la if u >= b) - a + 1

    def ext_hook(la, a, b):
        # extended hook in the k x m bounding box
        if b <= la[a-1]:
            return hook(la, a, b)
        laC = [m - la[k-i] for i in range(1, k+1)]   # complement
        return -hook(laC, k+1-a, m+1-b)

    Phi = R.zero()
    for s in range(k*m + 1):
        for la in Partitions(s, max_length=k, max_part=m):
            la = list(la) + [0]*(k - len(la))
            f = R.one()
            for a in range(1, k+1):
                for b in range(1, m+1):
                    h = ext_hook(la, a, b)
                    f *= (h - t) / h
            Phi += x**s * f
    return Phi

def Phi_CI(Phi_X, degrees):
    """Phi_Z(x,t) for Z ⊂ X a smooth CI of the given multidegree."""
    R = Phi_X.parent()
    x_var, t_var = R.gens()

    # Lift QQ[x,t] -> QQ[x][t]: t is the active variable, x lives in coeff ring.
    QQx = PolynomialRing(QQ, 'x'); x = QQx.gen()
    Rt  = PolynomialRing(QQx, 't'); t = Rt.gen()

    def lift(p):
        out = Rt.zero()
        for (i, j), c in p.dict().items():
            out += QQ(c) * x**i * t**j
        return out

    Phi = lift(Phi_X)

    for d in degrees:
        G = Phi - Phi(t - d)            # = (1 - T_d) Phi, in QQ[x][t]
        D = G.degree()                   # degree in t
        if D < 0:
            Phi = Rt.zero(); continue
        f_partial = Rt.zero()
        for k in range(D , -1, -1):
            shifted = (x * f_partial)(t - d)         # in QQ[x][t]
            rhs = G[k] + shifted[k]                  # in QQ[x]
            quo, rem = rhs.quo_rem(1 - x)            # univariate, honest
            assert rem == 0, f"non-exact at t^{k}: rem = {rem}"
            f_partial += quo * t**k
        Phi = f_partial

    # Push back to QQ[x,t] for return.
    out = R.zero()
    for j in range(Phi.degree() + 1 if Phi != 0 else 0):
        cx = Phi[j]
        for i in range(cx.degree() + 1):
            out += QQ(cx[i]) * x_var**i * t_var**j
    return out

PhiX = Phi_Gr(2, 7)
print("t-degree:", PhiX.degree(t))           # must be 10
print("Phi_X(0, 0):", PhiX.subs({x:0, t:0})) # must be 1
print("Phi_X(1, 0):", PhiX.subs({x:1, t:0})) # must be 21
print("Phi_X(0, t):")
print(PhiX.subs({x: 0}))                      # Hilbert poly of Gr(2,7)
print("Phi_X(x, 0):")
print(PhiX.subs({t: 0}))   # must be 1+x+2x^2+2x^3+3x^4+3x^5+3x^6+2x^7+2x^8+x^9+x^10

PhiZ = Phi_CI(PhiX, [1]*7)
print(PhiZ.subs({t:0}))         # -49*x - 49*x^2
print(PhiZ.subs({x:0, t:0}))    # 2  (= chi(O_Z) for a CY3)
PhiZ.degree(t)           # 3