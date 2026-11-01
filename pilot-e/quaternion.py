"""Definite quaternion algebra over F_q(t) ramified at {P, oo} (deg P = 1), Eichler orders of
level M, Brandt matrices, and Gross (Waldspurger) toric periods.

D = (nu, P): i^2 = nu (a non-square constant), j^2 = P, ij = -ji.  Ramified exactly at P and oo
(Hilbert symbols: nu is a non-square unit at P and at oo, and P has odd valuation at both).
O = A<1, i, j, ij> has reduced discriminant 4 nu P ~ P, so it is maximal.  Its unit group is
F_q(i)^* = F_{q^2}^*, the mass is 1/(q+1) = 1/#(O^*/F_q^*), so the class number is 1.

Hence for the Eichler order Lambda of level M (coprime to P) inside O,
  D^* \\ D^*_A / Lambda^_* F_A^*  =  P^1(A/M) / (O^*/F_q^*),
with O acting on row vectors through an isomorphism iota: O/MO -> M_2(A/M).
Functions on this finite set are the Brandt module; by Jacquet-Langlands its cuspidal part is
S(Gamma_0(P M)) new at P (with Steinberg at oo), and T_l acts by
  (T_l f)(x) = sum_{beta in O^* \\ O(l)} f(x iota(beta)),   O(l) = {beta in O : nrd beta in l F_q^*}.

Gross points of discriminant D0 (K = F(sqrt D0), P inert in K, primes of M split in K, oo not
split in K): y in O with y^2 = D0, with a fixed orientation at P (y mod jO = rho in F_{q^2}) and
at M (x_y = the line L in (A/M)^2 with L iota(y) = s L, s a fixed square root of D0 mod M).
Toric period P_D0(f) = sum_y f(x_y).
"""
import itertools
from flint import nmod_poly


class Quat:
    def __init__(self, p, P, nu):
        self.p, self.P, self.nu = p, P, nu
        self.one = nmod_poly([1], p)
        self.zero = nmod_poly([], p)

    def mul(self, x, y):
        nu, P = self.nu, self.P
        a0, a1, a2, a3 = x
        b0, b1, b2, b3 = y
        # basis 1, i, j, k=ij;  i^2=nu, j^2=P, k^2=-nu P, ij=k, ji=-k, ik = nu j, ki=-nu j, jk = -P i, kj = P i
        c0 = a0 * b0 + nu * a1 * b1 + P * a2 * b2 - nu * P * a3 * b3
        c1 = a0 * b1 + a1 * b0 - P * a2 * b3 + P * a3 * b2
        c2 = a0 * b2 + a2 * b0 + nu * a1 * b3 - nu * a3 * b1
        c3 = a0 * b3 + a3 * b0 + a1 * b2 - a2 * b1
        return (c0, c1, c2, c3)

    def nrd(self, x):
        a0, a1, a2, a3 = x
        return a0 * a0 - self.nu * a1 * a1 - self.P * a2 * a2 + self.nu * self.P * a3 * a3

    def conj(self, x):
        return (x[0], -x[1], -x[2], -x[3])


def mat_mul(X, Y, M):
    a, b, c, d = X
    e, f, g, h = Y
    return ((a * e + b * g) % M, (a * f + b * h) % M, (c * e + d * g) % M, (c * f + d * h) % M)


class Eichler:
    def __init__(self, p, P, M, nu=None):
        self.p, self.P, self.M = p, P, M
        if nu is None:
            nu = next(c for c in range(2, p) if pow(c, (p - 1) // 2, p) == p - 1)
        self.nuc = nu
        self.Q = Quat(p, P, nmod_poly([nu], p))
        dm = M.degree()
        self.res = [nmod_poly(list(cs), p) for cs in itertools.product(range(p), repeat=dm)]
        key = lambda r: tuple(int((r % M)[i]) for i in range(dm))
        self.key = key
        self.code = {key(r): i for i, r in enumerate(self.res)}
        units = [r for r in self.res if not r.is_zero() and r.gcd(M).degree() == 0]
        # P^1(A/M)
        orbit, reps = {}, []
        for c in self.res:
            for d in self.res:
                if c.gcd(d).gcd(M).degree() != 0:
                    continue
                if (key(c), key(d)) in orbit:
                    continue
                o = len(reps)
                reps.append((c, d))
                for u in units:
                    orbit[(key(u * c), key(u * d))] = o
        self.orbit, self.reps = orbit, reps
        # iota: i -> I0 = [[0, nu],[1, 0]], j -> X = [[a, -nu c],[c, -a]] with a^2 - nu c^2 = P mod M
        nuP = self.Q.nu
        I0 = (self.Q.zero, nuP % M, self.Q.one, self.Q.zero)
        X = None
        for a in self.res:
            for c in self.res:
                if ((a * a - nuP * c * c - P) % M).is_zero():
                    X = (a % M, (-nuP * c) % M, c % M, (-a) % M)
                    break
            if X:
                break
        assert X is not None
        self.I0, self.X = I0, X
        self.K0 = mat_mul(I0, X, M)
        self.one_m = (self.Q.one, self.Q.zero, self.Q.zero, self.Q.one)

    def iota(self, x):
        M = self.M
        out = [self.Q.zero] * 4
        for coef, B in zip(x, (self.one_m, self.I0, self.X, self.K0)):
            for k in range(4):
                out[k] = (out[k] + coef * B[k]) % M
        return tuple(out)

    def act(self, idx, B):
        c, d = self.reps[idx]
        a, b, cc, dd = B
        return self.orbit[(self.key(c * a + d * cc), self.key(c * b + d * dd))]

    def units(self):
        p = self.p
        out = []
        for a in range(p):
            for b in range(p):
                if a or b:
                    out.append((nmod_poly([a], p), nmod_poly([b], p), self.Q.zero, self.Q.zero))
        return out

    def classes(self):
        """orbits of O^*/F_q^* on P^1(A/M); returns (list of orbits, index map, stabiliser sizes)."""
        U = [self.iota(u) for u in self.units()]
        N = len(self.reps)
        cls = [-1] * N
        orbs = []
        for x in range(N):
            if cls[x] >= 0:
                continue
            orb = sorted(set(self.act(x, u) for u in U))
            for y in orb:
                cls[y] = len(orbs)
            orbs.append(orb)
        q = self.p
        stab = [(q + 1) // len(o) if (q + 1) % len(o) == 0 else None for o in orbs]
        self.cls, self.orbs, self.stab = cls, orbs, stab
        return orbs

    def elements_of_norm(self, ell):
        """O(ell) / O^* : one beta per left ideal O beta of norm ell (ell monic, prime to P M)."""
        p, Q = self.p, self.Q
        dl = ell.degree()
        # deg nrd = max(2 max(deg x0, deg x1), 1 + 2 max(deg x2, deg x3)) = dl
        e01 = dl // 2
        e23 = (dl - 1) // 2
        polys = lambda e: [nmod_poly(list(cs), p) for cs in itertools.product(range(p), repeat=e + 1)] if e >= 0 else [Q.zero]
        U = self.units()
        seen = set()
        out = []
        for x0 in polys(e01):
            for x1 in polys(e01):
                for x2 in polys(e23):
                    for x3 in polys(e23):
                        b = (x0, x1, x2, x3)
                        n = Q.nrd(b)
                        if n.degree() != dl or not (n % ell).is_zero():
                            continue
                        k = tuple(tuple(int(c) for c in z.coeffs()) for z in b)
                        if k in seen:
                            continue
                        for u in U:
                            ub = Q.mul(u, b)
                            seen.add(tuple(tuple(int(c) for c in z.coeffs()) for z in ub))
                        out.append(b)
        assert len(out) == p ** dl + 1, (len(out), ell)
        return out

    def brandt(self, ell):
        """Matrix of T_ell on functions on classes, B[i][j] = # of beta with x_i iota(beta) in class j."""
        betas = [self.iota(b) for b in self.elements_of_norm(ell)]
        h = len(self.orbs)
        B = [[0] * h for _ in range(h)]
        for i, orb in enumerate(self.orbs):
            x = orb[0]
            for be in betas:
                B[i][self.cls[self.act(x, be)]] += 1
        return B

    def sqrt_mod(self, D0):
        """a square root s of D0 mod M (M's primes split in K)."""
        for s in self.res:
            if ((s * s - D0) % self.M).is_zero():
                return s
        return None

    def gross_points(self, D0):
        """List of P^1(A/M)-indices x_y over y in O with y^2 = D0, fixed orientations."""
        p, Q, M, P = self.p, self.Q, self.M, self.P
        dD = D0.degree()
        s = self.sqrt_mod(D0)
        assert s is not None
        # orientation at P: y = x1 i + (x2 + x3 i) j with x0 = 0; y mod jO = x1(P) i in F_{q^2}
        e01 = dD // 2
        e23 = (dD - 1) // 2
        polys = lambda e: [nmod_poly(list(cs), p) for cs in itertools.product(range(p), repeat=e + 1)] if e >= 0 else [Q.zero]
        pts = []
        rho = None
        target = D0
        for x1 in polys(e01):
            for x2 in polys(e23):
                for x3 in polys(e23):
                    y = (Q.zero, x1, x2, x3)
                    # y^2 = -nrd(y) for trace zero
                    if not (-Q.nrd(y) - target).is_zero():
                        continue
                    r = int((x1 % P)[0]) if not (x1 % P).is_zero() else 0
                    if rho is None:
                        rho = r
                    if r != rho:
                        continue
                    # eigenline of iota(y) for eigenvalue s: row vector v with v (Y - s) = 0
                    Y = self.iota(y)
                    a, b, c, d = Y
                    a, d = (a - s) % M, (d - s) % M
                    # v = (v1, v2): v1 a + v2 c = 0, v1 b + v2 d = 0 -> try v = (c, -a) or (d, -b)
                    cand = None
                    for v in ((c, -a), (d, -b)):
                        v1, v2 = v[0] % M, v[1] % M
                        if v1.gcd(v2).gcd(M).degree() == 0:
                            if ((v1 * a + v2 * c) % M).is_zero() and ((v1 * b + v2 * d) % M).is_zero():
                                cand = (v1, v2)
                                break
                    if cand is None:
                        # M composite with mixed kernel: solve by brute force
                        for idx, (v1, v2) in enumerate(self.reps):
                            if ((v1 * a + v2 * c) % M).is_zero() and ((v1 * b + v2 * d) % M).is_zero():
                                cand = (v1, v2)
                                break
                    assert cand is not None
                    pts.append(self.orbit[(self.key(cand[0]), self.key(cand[1]))])
        return pts
