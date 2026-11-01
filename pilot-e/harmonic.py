"""Cuspidal harmonic cochains for Gamma_0(n) in GL_2(F_q[t]) and their Hecke operators.

Everything is computed from scratch on the Bruhat-Tits tree T of PGL_2(F_q((1/t))).

Conventions
-----------
* A = F_q[t] (q = p prime here), v_k = class of diag(t^k, 1) O_oo^2, k >= 0.
  GL_2(A)\\T is the half line v_0 - v_1 - v_2 - ...; e_k is the edge v_k -> v_{k+1}.
* Stab(v_0) = GL_2(F_q); for k >= 1, Stab(v_k) = {[[a,b],[0,d]] : a,d in F_q^*, deg b <= k}.
  Stab(e_0) = B(F_q), Stab(e_k) = Stab(v_k) for k >= 1.
* Gamma_0(n)\\GL_2(A) = P^1(A/n) via the bottom row.  A Gamma_0(n)-invariant cochain f is
  the family c_k(x) = f(g e_k), x = bottom row of g.
* Harmonicity at g v_k (k >= 1): c_k(x) = sum_{beta in F_q} c_{k-1}(x [[1, beta t^k],[0,1]]).
  Harmonicity at g v_0: sum_{s in GL_2(F_q)/B(F_q)} c_0(x s) = 0.
  So a cochain is determined by c_0, a B(F_q)-invariant function on P^1(A/n).
* Cuspidal: finite support mod Gamma_0(n), i.e. c_K = 0 for K large.
* Hecke: (T_p f)(e) = f([[p,0],[0,1]] e) + sum_{deg b < deg p} f([[1,b],[0,p]] e).
  Evaluating f on an arbitrary edge uses `reduce_vertex`, which finds gamma in GL_2(A) and k
  with M O^2 = gamma v_k, by column-reducing adj(M) over F_q[t] (Popov form).
"""
import itertools
from flint import nmod_poly, fmpz_mat, fmpq_mat, fmpq


class Field:
    def __init__(self, p):
        self.p = p
        self.zero = nmod_poly([], p)
        self.one = nmod_poly([1], p)
        self.t = nmod_poly([0, 1], p)

    def P(self, coeffs):
        return nmod_poly(list(coeffs), self.p)

    def polys(self, maxdeg):
        """All polynomials of degree <= maxdeg (maxdeg = -1 gives just 0)."""
        p = self.p
        for cs in itertools.product(range(p), repeat=maxdeg + 1):
            yield nmod_poly(list(cs), p)

    def monic(self, d):
        p = self.p
        for cs in itertools.product(range(p), repeat=d):
            yield nmod_poly(list(cs) + [1], p)

    def irreducibles(self, d):
        for f in self.monic(d):
            fac = f.factor()[1]
            if len(fac) == 1 and fac[0][1] == 1:
                yield f


def deg(f):
    return f.degree()  # -1 for zero


# ---------- 2x2 polynomial matrices as tuples (a, b, c, d) ----------

def mmul(X, Y):
    a, b, c, d = X
    e, f, g, h = Y
    return (a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h)


def adj(X):
    a, b, c, d = X
    return (d, -b, -c, a)


def det(X):
    a, b, c, d = X
    return a * d - b * c


def lead(f, dd):
    """coefficient of t^dd in f"""
    return int(f[dd]) if 0 <= dd <= f.degree() else 0


def reduce_vertex(M, F):
    """Return (gamma, k) with gamma in GL_2(A) (unit det) and M O^2 ~ gamma v_k."""
    N = adj(M)
    a, b, c, d = N
    g = (F.one, F.zero, F.zero, F.one)
    p = F.p
    while True:
        d1 = max(deg(a), deg(c))
        d2 = max(deg(b), deg(d))
        L1 = (lead(a, d1), lead(c, d1))
        L2 = (lead(b, d2), lead(d, d2))
        if (L1[0] * L2[1] - L1[1] * L2[0]) % p != 0:
            break
        # proportional leading vectors: reduce the higher column
        if d1 >= d2:
            # col1 -= lam t^(d1-d2) col2, lam = L1/L2
            i = 0 if L2[0] else 1
            lam = L1[i] * pow(L2[i], p - 2, p) % p
            mon = F.P([0] * (d1 - d2) + [lam])
            a, c = a - mon * b, c - mon * d
            g = (g[0] - mon * g[1], g[1], g[2] - mon * g[3], g[3])
        else:
            i = 0 if L1[0] else 1
            lam = L2[i] * pow(L1[i], p - 2, p) % p
            mon = F.P([0] * (d2 - d1) + [lam])
            b, d = b - mon * a, d - mon * c
            g = (g[0], g[1] - mon * g[0], g[2], g[3] - mon * g[2])
    if d1 > d2:
        g = (g[1], g[0], g[3], g[2])
        d1, d2 = d2, d1
    return g, d2 - d1


def inv_unimodular(g):
    a, b, c, d = g
    D = det(g)
    assert D.degree() == 0
    p = D.modulus()
    ui = pow(int(D[0]), p - 2, p)
    return (d * ui, -b * ui, -c * ui, a * ui)


def in_stab_v1(h):
    """h in GL_2(A) (unit det): is h v_1 = v_1 ?"""
    a, b, c, d = h
    return c.is_zero() and a.degree() == 0 and d.degree() == 0 and b.degree() <= 1


class Level:
    def __init__(self, F, n):
        self.F = F
        self.n = n
        self.dn = n.degree()
        p = F.p
        self.p = p
        dn = self.dn
        # residues mod n, encoded as ints
        self.res = [F.P(cs) for cs in itertools.product(range(p), repeat=dn)]
        self.code = {}
        for i, r in enumerate(self.res):
            self.code[self._key(r)] = i
        units = [i for i, r in enumerate(self.res) if (not r.is_zero()) and r.gcd(n).degree() == 0]
        self.units = units
        R = len(self.res)
        # multiplication table mod n (as index arithmetic)
        self.pairs = {}
        orbit = {}
        reps = []
        for ic, c in enumerate(self.res):
            for id_, dd in enumerate(self.res):
                if c.gcd(dd).gcd(n).degree() != 0:
                    continue
                if (ic, id_) in orbit:
                    continue
                o = len(reps)
                reps.append((c, dd))
                for iu in units:
                    u = self.res[iu]
                    orbit[(self.idx(u * c), self.idx(u * dd))] = o
        self.orbit = orbit
        self.reps = reps
        self.N = len(reps)

    def _key(self, r):
        r = r % self.n
        cs = [int(r[i]) for i in range(self.dn)]
        return tuple(cs)

    def idx(self, r):
        return self.code[self._key(r)]

    def pt(self, c, d):
        """P^1(A/n) index of the row (c : d)."""
        return self.orbit[(self.idx(c), self.idx(d))]

    # ----- linear maps on functions on P^1(A/n) -----
    def S(self, k):
        """(S_k g)(x) = sum_beta g(x [[1, beta t^k],[0,1]]) as list of lists of indices."""
        F = self.F
        tk = F.t ** k
        out = []
        for (c, d) in self.reps:
            out.append([self.pt(c, d + F.P([b]) * tk * c) for b in range(self.p)])
        return out

    def build(self, K=None):
        """Compute the space of cuspidal harmonic cochains."""
        F, p = self.F, self.p
        if K is None:
            K = self.dn + 2
        self.K = K
        N = self.N
        # B(F_q)-orbits on P^1 -> variables
        var = [-1] * N
        nv = 0
        for i, (c, d) in enumerate(self.reps):
            if var[i] >= 0:
                continue
            stack = [i]
            var[i] = nv
            while stack:
                j = stack.pop()
                cj, dj = self.reps[j]
                nbrs = [self.pt(cj, dj + F.P([b]) * cj) for b in range(1, p)]
                nbrs += [self.pt(F.P([a]) * cj, dj) for a in range(1, p)]
                for m in nbrs:
                    if var[m] < 0:
                        var[m] = nv
                        stack.append(m)
            nv += 1
        self.var = var
        self.nv = nv
        self.varrep = [var.index(v) for v in range(nv)]
        # c_k as integer matrices N x nv : C[k][x] = list of coefficients
        C0 = [[1 if var[x] == v else 0 for v in range(nv)] for x in range(N)]
        self.C = [C0]
        for k in range(1, K + 2):
            Sk = self.S(k)
            prev = self.C[-1]
            new = []
            for x in range(N):
                row = [0] * nv
                for y in Sk[x]:
                    py = prev[y]
                    for v in range(nv):
                        row[v] += py[v]
                new.append(row)
            self.C.append(new)
        # constraints
        rows = []
        for x, (c, d) in enumerate(self.reps):
            idxs = [self.pt(c + F.P([a]) * d, d) for a in range(p)] + [self.pt(d, c)]
            row = [0] * nv
            for y in idxs:
                row[var[y]] += 1
            rows.append(row)
        for x in range(N):
            rows.append(self.C[K][x])
        A = fmpz_mat(rows)
        X, nul = A.nullspace()
        basis = [[int(X[i, j]) for i in range(nv)] for j in range(nul)]
        self.basis = basis
        self.dim = nul
        # stability check: c_{K-1} and c_{K+1}
        return nul

    def ck_value(self, k, x, c0):
        """c_k(x) for the cochain with c_0-variables c0 (list), k arbitrary."""
        while k >= len(self.C):
            # extend lazily
            Sk = self.S(len(self.C))
            prev = self.C[-1]
            new = []
            for xx in range(self.N):
                row = [0] * self.nv
                for y in Sk[xx]:
                    for v in range(self.nv):
                        row[v] += prev[y][v]
                new.append(row)
            self.C.append(new)
        row = self.C[k][x]
        return row

    # ----- edge evaluation as a linear functional on the c_0-variables -----
    def edge_functional(self, M1, M2):
        """Return (sign, k, x) with f(edge [M1]->[M2]) = sign * c_k(x)."""
        F = self.F
        g1, k1 = reduce_vertex(M1, F)
        g2, k2 = reduce_vertex(M2, F)
        if k2 == k1 + 1:
            sign, g, k = 1, g1, k1
            gb = g2
        elif k1 == k2 + 1:
            sign, g, k = -1, g2, k2
            gb = g1
        else:
            raise ValueError("not adjacent: %d %d" % (k1, k2))
        if k == 0:
            gbi = inv_unimodular(gb)
            found = None
            cands = [(F.one, F.zero, F.P([a]), F.one) for a in range(self.p)] + [(F.zero, F.one, F.one, F.zero)]
            for s in cands:
                gs = mmul(g, s)
                if in_stab_v1(mmul(gbi, gs)):
                    found = gs
                    break
            assert found is not None
            g = found
        x = self.pt(g[2], g[3])
        return sign, k, x

    def eval_edge(self, M1, M2, c0):
        s, k, x = self.edge_functional(M1, M2)
        row = self.ck_value(k, x, c0)
        return s * sum(r * c for r, c in zip(row, c0))

    def lift(self, c, d):
        """A matrix in SL_2(A) whose bottom row is congruent to (c, d) mod n (up to unit)."""
        F, n = self.F, self.n
        if c.is_zero():
            c = n
        # search d' = d + m n with gcd(c, d') = 1
        for dm in range(0, 4):
            for m in F.polys(dm):
                dd = d + m * n
                if c.gcd(dd).degree() == 0:
                    g, s, tt = c.xgcd(dd)  # s c + tt dd = g (unit)
                    gi = pow(int(g[0]), self.p - 2, self.p)
                    # [[a, b],[c, dd]] with a dd - b c = 1: a = tt/g, b = -s/g
                    a = tt * gi
                    b = -s * gi
                    M = (a, b, c, dd)
                    assert det(M) == F.one
                    return M
        raise RuntimeError("lift failed")

    def hecke_matrix_vars(self, P, vars_=None):
        """T_P on c_0-variables: returns nv x nv integer matrix (rows = variable reps).
        With vars_ given, only those rows."""
        F = self.F
        dP = P.degree()
        alphas = [(P, F.zero, F.zero, F.one)] + [(F.one, b, F.zero, P) for b in F.polys(dP - 1)]
        T = []
        diag_t = (F.t, F.zero, F.zero, F.one)
        for v in (range(self.nv) if vars_ is None else vars_):
            x = self.varrep[v]
            c, d = self.reps[x]
            g = self.lift(c, d)
            row = [0] * self.nv
            for al in alphas:
                M1 = mmul(al, g)
                M2 = mmul(M1, diag_t)
                s, k, y = self.edge_functional(M1, M2)
                r = self.ck_value(k, y, None)
                for i in range(self.nv):
                    row[i] += s * r[i]
            T.append(row)
        return T

    def hecke_on_cusp(self, P):
        """Matrix of T_P on the cusp form basis (acting on coordinate column vectors)."""
        T = fmpq_mat(self.hecke_matrix_vars(P))
        B = fmpq_mat(self.nv, self.dim, [fmpq(self.basis[j][i]) for i in range(self.nv) for j in range(self.dim)])
        TB = T * B
        # solve B X = TB  (least squares exact via normal equations, B has full column rank)
        Bt = B.transpose()
        X = (Bt * B).solve(Bt * TB)
        assert B * X == TB, "cusp space not Hecke stable?"
        return X
