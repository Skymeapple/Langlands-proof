"""Elliptic curves y^2 = x^3 + a2 x^2 + a4 x + a6 over F_p(t), p odd.

* Tate's algorithm (Silverman, Advanced Topics IV.9.4; Cremona's I_n* loop), specialised to
  a1 = a3 = 0, at any finite place P (monic irreducible) and at oo (via s = 1/t).
  Conductor exponent from Ogg's formula f = v(Delta) + 1 - m, which Tate's algorithm returns
  case by case; this is valid in every residue characteristic, including the wild case p = 3.
* Frobenius traces a_P = q^deg P + 1 - #E(F_P) by direct point counting with finite field tables.
"""
import itertools
import numpy as np
from flint import nmod_poly


def disc_data(a2, a4, a6):
    b2 = 4 * a2
    b4 = 2 * a4
    b6 = 4 * a6
    b8 = 4 * a2 * a6 - a4 * a4
    D = -b2 * b2 * b8 - 8 * b4 * b4 * b4 - 27 * b6 * b6 + 9 * b2 * b4 * b6
    return b2, b4, b6, b8, D


def val(f, P):
    if f.is_zero():
        return 10 ** 6
    v = 0
    while True:
        q, r = divmod(f, P)
        if not r.is_zero():
            return v
        f = q
        v += 1


class ResidueField:
    """F_p[t]/P with element tables."""
    def __init__(self, P):
        self.P = P
        self.p = p = P.modulus()
        self.d = d = P.degree()
        self.q = q = p ** d
        self.elts = [nmod_poly(list(cs), p) for cs in itertools.product(range(p), repeat=d)]
        # code: little-endian digits; itertools.product is big-endian in last index -> build dict
        self.code = {}
        for i, e in enumerate(self.elts):
            self.code[self.key(e)] = i
        mul = np.zeros((q, q), dtype=np.int32)
        add = np.zeros((q, q), dtype=np.int32)
        for i, e in enumerate(self.elts):
            for j, f in enumerate(self.elts):
                if j < i:
                    mul[i, j] = mul[j, i]
                    add[i, j] = add[j, i]
                    continue
                mul[i, j] = self.code[self.key((e * f) % P)]
                add[i, j] = self.code[self.key(e + f)]
        self.mul, self.add = mul, add
        # quadratic character
        chi = np.zeros(q, dtype=np.int64)
        sq = set()
        for i in range(q):
            sq.add(int(mul[i, i]))
        for i in range(q):
            if self.elts[i].is_zero():
                chi[i] = 0
            else:
                chi[i] = 1 if i in sq else -1
        self.chi = chi
        self.squares = sq
        self.allidx = np.arange(q)

    def key(self, e):
        e = e % self.P
        return tuple(int(e[i]) for i in range(self.d))

    def idx(self, f):
        return self.code[self.key(f)]

    def count_points(self, a2, a4, a6):
        """#E(F_P) for the reduced cubic, including the singular point if any and oo."""
        m, ad = self.mul, self.add
        x = self.allidx
        A2, A4, A6 = self.idx(a2), self.idx(a4), self.idx(a6)
        x2 = m[x, x]
        x3 = m[x2, x]
        y = ad[ad[ad[x3, m[x2, A2]], m[x, A4]], A6]
        return int(self.q + np.sum(self.chi[y]) + 1)

    def is_square(self, f):
        return self.idx(f) in self.squares


def kinv(z, P):
    g, s, _ = z.xgcd(P)
    assert g.degree() == 0
    p = P.modulus()
    return (s * pow(int(g[0]), p - 2, p)) % P


def k_is_square(z, P):
    p = P.modulus()
    Q = p ** P.degree()
    return z.pow_mod((Q - 1) // 2, P).is_one()


def _pmod(f, P):
    f = [c % P for c in f]
    while f and f[-1].is_zero():
        f.pop()
    return f


def _kpoly_rem(f, g, P):
    f = list(f)
    ig = kinv(g[-1], P)
    while len(f) >= len(g):
        c = (f[-1] * ig) % P
        sh = len(f) - len(g)
        for i in range(len(g)):
            f[sh + i] = (f[sh + i] - c * g[i]) % P
        f = _pmod(f, P)
        if not f:
            break
    return f


def multiple_root(f, P):
    """f = [c0,c1,c2,c3] (c3 = 1) over k = F_p[t]/P. Return a root of gcd(f, f') or None."""
    p = P.modulus()
    f = _pmod(f, P)
    df = _pmod([f[1], 2 * f[2], 3 * f[3]], P)
    if not df:
        # char 3, f = X^3 + c0: triple root -c0^(1/3)
        d = P.degree()
        c = f[0] if not f[0].is_zero() else f[0]
        r = (-c).pow_mod(3 ** (d - 1), P) if not c.is_zero() else c
        return r
    a, b = f, df
    while b:
        a, b = b, _kpoly_rem(a, b, P)
    g = a
    if len(g) == 1:
        return None
    if len(g) == 2:
        return (-g[0] * kinv(g[1], P)) % P
    if len(g) == 3:
        return (-g[1] * kinv(2 * g[2], P)) % P
    raise AssertionError


def translate(a2, a4, a6, r):
    return (a2 + 3 * r,
            a4 + 2 * a2 * r + 3 * r * r,
            a6 + a4 * r + a2 * r * r + r * r * r)


def exdiv(f, g):
    q, r = divmod(f, g)
    assert r.is_zero()
    return q


def tate(a2, a4, a6, P, K):
    """Tate's algorithm at P. K is the ResidueField of P.
    Returns dict(kodaira, f, m, vD, split (mult only), minimal)."""
    p = P.modulus()
    one = nmod_poly([1], p)
    minimal = True
    while True:
        b2, b4, b6, b8, D = disc_data(a2, a4, a6)
        vD = val(D, P)
        if vD == 0:
            return dict(kod='I0', f=0, m=1, vD=0, minimal=minimal)
        # multiple root of the reduced cubic
        x0 = multiple_root([a6 % P, a4 % P, a2 % P, one], P)
        assert x0 is not None
        a2, a4, a6 = translate(a2, a4, a6, x0)
        b2, b4, b6, b8, D = disc_data(a2, a4, a6)
        if val(b2, P) == 0:
            split = k_is_square(a2 % P, P)
            return dict(kod='I%d' % vD, f=1, m=vD, vD=vD, split=bool(split), minimal=minimal)
        if val(a6, P) < 2:
            return dict(kod='II', f=vD, m=1, vD=vD, minimal=minimal)
        if val(b8, P) < 3:
            return dict(kod='III', f=vD - 1, m=2, vD=vD, minimal=minimal)
        if val(b6, P) < 3:
            return dict(kod='IV', f=vD - 2, m=3, vD=vD, minimal=minimal)
        P2, P3 = P * P, P * P * P
        assert val(a2, P) >= 1 and val(a4, P) >= 2 and val(a6, P) >= 3
        c2, c1, c0 = exdiv(a2, P) % P, exdiv(a4, P2) % P, exdiv(a6, P3) % P
        al = multiple_root([c0, c1, c2, one], P)
        if al is None:
            return dict(kod='I0*', f=vD - 4, m=5, vD=vD, minimal=minimal)
        # triple root?  P(T) = (T - al)^3 mod P
        triple = ((c2 + 3 * al) % P).is_zero() and ((c1 - 3 * al * al) % P).is_zero() and \
                 ((c0 + al * al * al) % P).is_zero()
        if not triple:
            a2, a4, a6 = translate(a2, a4, a6, al * P)
            mx = P2
            my = P2
            mm = 1
            while True:
                xa6 = exdiv(a6, mx * my) % P
                if not xa6.is_zero():
                    break
                my = my * P
                mm += 1
                xa2 = exdiv(a2, P) % P
                xa4 = exdiv(a4, P * mx) % P
                xa6 = exdiv(a6, mx * my) % P
                dsc = (xa4 * xa4 - 4 * xa2 * xa6) % P
                if not dsc.is_zero():
                    break
                # double root X = -xa4 / (2 xa2) in K
                X = (-xa4 * kinv(2 * xa2, P)) % P
                a2, a4, a6 = translate(a2, a4, a6, X * mx)
                mx = mx * P
                mm += 1
            return dict(kod='I%d*' % mm, f=vD - 4 - mm, m=5 + mm, vD=vD, minimal=minimal)
        a2, a4, a6 = translate(a2, a4, a6, al * P)
        P4 = P2 * P2
        if not (exdiv(a6, P4) % P).is_zero():
            return dict(kod='IV*', f=vD - 6, m=7, vD=vD, minimal=minimal)
        if val(a4, P) < 4:
            return dict(kod='III*', f=vD - 7, m=8, vD=vD, minimal=minimal)
        if val(a6, P) < 6:
            return dict(kod='II*', f=vD - 8, m=9, vD=vD, minimal=minimal)
        # non-minimal
        minimal = False
        a2, a4, a6 = exdiv(a2, P2), exdiv(a4, P4), exdiv(a6, P4 * P2)


def at_infinity(a2, a4, a6):
    """Model in s = 1/t: a_i(s) = s^i a_i(1/s); requires deg a_i <= i."""
    p = a2.modulus()
    out = []
    for f, i in ((a2, 2), (a4, 4), (a6, 6)):
        assert f.degree() <= i
        cs = [int(f[j]) for j in range(i + 1)]
        out.append(nmod_poly(cs[::-1], p))
    return out


_RF = {}


def residue_field(P):
    key = (P.modulus(), tuple(int(c) for c in P.coeffs()))
    if key not in _RF:
        _RF[key] = ResidueField(P)
    return _RF[key]


def local_data(a2, a4, a6, D=None):
    """Tate's algorithm at all bad finite places and at oo. Returns list of (place, data)."""
    p = a2.modulus()
    if D is None:
        D = disc_data(a2, a4, a6)[4]
    out = []
    for P, e in D.factor()[1]:
        out.append((P, tate(a2, a4, a6, P, None)))
    s = nmod_poly([0, 1], p)
    b2, b4, b6 = at_infinity(a2, a4, a6)
    out.append(('oo', tate(b2, b4, b6, s, None)))
    return out
