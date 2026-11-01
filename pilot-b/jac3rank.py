"""3-rank of J(F_p) for a genus 2 curve y^2 = F(x) over F_p (p odd), exactly.

Method: move a rational Weierstrass point to infinity (needs a root of F mod p, or deg F = 5),
make the quintic monic, then use Cantor's algorithm on Mumford pairs (u, v). The full Sylow
3-subgroup S of J(F_p) (order 3^v known from the L-polynomial) is generated from random
elements until the generated group has order 3^v, then S[3] is counted by enumeration.
Everything is exact: the result is certified once the generated group reaches order 3^v.
"""
import random
from g2lib import pari

MAXSYLOW = 3 ** 7


class Jac:
    def __init__(self, F, p):
        self.p = p
        self.F = F  # monic quintic over F_p (PARI polynomial with Mod coeffs)
        self.one = pari(f"Mod(1,{p})")
        self.zero = (pari(1) * self.one, pari(0) * self.one)

    def key(self, D):
        return (str(pari.lift(D[0])), str(pari.lift(D[1])))

    def reduce(self, u, v):
        F = self.F
        while pari.poldegree(u) > 2:
            u2 = (F - v * v) / u
            u2 = pari.Pol(u2)
            v = (-v) % u2
            u = u2
        lc = pari.pollead(u)
        u = u / lc
        v = v % u
        return (u, v)

    def add(self, D1, D2):
        u1, v1 = D1
        u2, v2 = D2
        F = self.F
        # d1 = gcd(u1,u2) = e1 u1 + e2 u2
        r = pari.gcdext(u1, u2)
        e1, e2, d1 = r[0], r[1], r[2]
        r2 = pari.gcdext(d1, v1 + v2)
        c1, c2, d = r2[0], r2[1], r2[2]
        s1, s2, s3 = c1 * e1, c1 * e2, c2
        lc = pari.pollead(d)
        d, s1, s2, s3 = d / lc, s1 / lc, s2 / lc, s3 / lc
        u = pari.Pol(u1 * u2 / (d * d))
        v = (s1 * u1 * v2 + s2 * u2 * v1 + s3 * (v1 * v2 + F)) / d
        v = pari.Pol(v) % u
        return self.reduce(u, v)

    def mul(self, n, D):
        R = self.zero
        Q = D
        while n:
            if n & 1:
                R = self.add(R, Q)
            Q = self.add(Q, Q)
            n >>= 1
        return R

    def random_point(self, attempts=50):
        p = self.p
        for _ in range(attempts):
            x0 = random.randrange(p)
            val = pari.subst(self.F, "x", x0)
            if pari.issquare(val):
                y0 = pari.sqrt(val) if val != 0 else 0 * self.one
                return (pari(f"x-{x0}") * self.one, pari(y0) * self.one + 0 * pari("x"))
        return None

    def random_quadratic(self):
        """Degree-2 divisor supported on a conjugate pair of points over F_{p^2}."""
        p = self.p
        while True:
            u = pari(f"x^2 + {random.randrange(p)}*x + {random.randrange(p)}") * self.one
            if not pari.polisirreducible(u):
                continue
            t = pari.ffgen(u, "t")
            val = pari.subst(pari.lift(self.F), "x", t)
            if not pari.issquare(val):
                continue
            s = pari.sqrt(val)
            v = pari.Pol(pari("(s)->s.pol")(s))
            v = pari.subst(v, "t", pari("x")) * self.one
            assert ((v * v - self.F) % u) == 0
            return (u, v % u)

    def random_divisor(self):
        if random.random() < 0.5:
            P, Q = self.random_point(), self.random_point()
            if P is not None and Q is not None:
                return self.add(P, Q)
        return self.random_quadratic()


def to_odd_model(F, p):
    """Given y^2 = F (deg 5 or 6, squarefree mod p), return monic quintic model over F_p or None."""
    Fp = F * pari(f"Mod(1,{p})")
    deg = int(pari.poldegree(Fp))
    if deg == 6:
        roots = pari.polrootsmod(pari.lift(Fp), p)
        if len(roots) == 0:
            return None
        r = roots[0]
        # x = r + 1/t : y^2 = F(r+1/t) ; multiply by t^6 -> quintic in t (since F(r)=0)
        G = pari.substpol(Fp, "x", pari(f"({r}) + 1/x"))
        G = pari.Pol(G * pari("x^6"))
        Fp = G
        deg = int(pari.poldegree(Fp))
    if deg != 5:
        return None
    c = pari.pollead(Fp)
    # Y^2 = c^4 F(X/c)  (monic)
    G = pari.Pol(pari.substpol(Fp, "x", pari("x") / c) * c ** 4)
    return G


def sylow3_rank(F, p, order, tries=400):
    """F: y^2 = F over Z; order = #J(F_p). Returns 3-rank or None if no odd model available."""
    v = 0
    n = order
    while n % 3 == 0:
        n //= 3
        v += 1
    if v <= 1:
        return v
    if 3 ** v > MAXSYLOW:
        return None
    G = to_odd_model(F, p)
    if G is None:
        return None
    J = Jac(G, p)
    m = order // 3 ** v
    elems = {J.key(J.zero): J.zero}
    for _ in range(tries):
        if len(elems) == 3 ** v:
            break
        Q = J.mul(m, J.random_divisor())
        if J.key(Q) in elems:
            continue
        # extend subgroup by Q: new = {a + k Q}
        new = dict(elems)
        frontier = list(elems.values())
        R = Q
        while J.key(R) not in elems:
            for a in frontier:
                s = J.add(a, R)
                new[J.key(s)] = s
            R = J.add(R, Q)
        elems = new
        # closure (subgroup generated) - iterate until closed under adding Q
        changed = True
        while changed:
            changed = False
            for a in list(elems.values()):
                s = J.add(a, Q)
                k = J.key(s)
                if k not in elems:
                    elems[k] = s
                    changed = True
    if len(elems) != 3 ** v:
        raise RuntimeError(f"Sylow-3 generation failed p={p} got {len(elems)} want {3**v}")
    zk = J.key(J.zero)
    n3 = sum(1 for D in elems.values() if J.key(J.mul(3, D)) == zk)
    r = 0
    while 3 ** r < n3:
        r += 1
    assert 3 ** r == n3
    return r
