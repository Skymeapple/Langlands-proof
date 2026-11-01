"""L(1, pi, Ad) = L(Sym^2 E, q^-2) from Frobenius traces of Pilot E's curves (shared helpers)."""
import ast
from fractions import Fraction as Fr
from flint import nmod_poly


def mul(a, b, B):
    out = [Fr(0)] * (B + 1)
    for i, x in enumerate(a[:B + 1]):
        if x:
            for j, y in enumerate(b[:B + 1 - i]):
                out[i + j] += x * y
    return out


def inv(poly, B):
    poly = list(poly) + [0] * (B + 1)
    out = [Fr(0)] * (B + 1); out[0] = Fr(1)
    for i in range(1, B + 1):
        out[i] = -sum(poly[j] * out[i - j] for j in range(1, i + 1))
    return out


def partial_sym2(c, B, q):
    """Euler product of L(Sym^2 E, T) mod T^(B+1) over good and multiplicative places (incl. oo);
    returns (series, list of additive places)."""
    ap = {tuple(ast.literal_eval(k)): v for k, v in c['ap'].items()}
    n = nmod_poly(c['n'], q)
    bad = {tuple(int(x) for x in P.coeffs()): e for P, e in n.factor()[1]}
    ser = [Fr(1)] + [Fr(0)] * B
    add = [k for k, e in bad.items() if e >= 2]
    for key, a in ap.items():
        d = len(key) - 1
        if d > B or key in add:
            continue
        Q = q ** d
        if key in bad:
            poly = [1] + [0] * (d - 1) + [-1]            # Sym^2 of Steinberg: invariant line, Frobenius a^2 = 1
        else:
            s2 = a * a - 2 * Q
            poly = [0] * (3 * d + 1)
            poly[0] = 1; poly[d] = -(s2 + Q); poly[2 * d] = Q * s2 + Q * Q; poly[3 * d] = -Q ** 3
        ser = mul(ser, inv(poly, B), B)
    ser = mul(ser, inv([1, -1], B), B)                    # oo: multiplicative, degree 1
    return ser, add




def L_adjoint(c, q, B):
    """L^{add}(1, pi, Ad): adjoint L-value without Euler factors at additive places (see gross_derived.py)."""
    ser, add = partial_sym2(c, B, q)
    if not add:
        assert all(x == 0 for x in ser[3:])
        return sum(x / Fr(q) ** (2 * i) for i, x in enumerate(ser[:3]))
    assert len(add) == 1 and len(add[0]) == 2 and all(x == 0 for x in ser[2:])
    beta = -ser[1]
    assert beta in (1, q, -q)
    return 1 - beta / Fr(q) ** 2
