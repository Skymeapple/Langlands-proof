"""Ichino local integral at l for the conductor-2 classes with NO supercuspidal factor, using the
induced model.  pi = Ind(mu |.|^s, mu^-1 |.|^-s) (normalised), mu tame with mu(varpi) = u:
   ps_e   : mu|O^x of order e (q = 1 mod e), s = 0, unitary;
   St x chi: mu = chi quadratic, s = 1/2 (St x chi is the subrepresentation).
The contragredient is Ind(mu^-1, -s) with the pairing int_K f f~.  K^+-fixed vectors <-> functions F on
P^1(F_q):  f(g) = mu(det g/d^2)|det g/d^2|^{s+1/2} F(c/d mod varpi)  if |d| >= |c|,
           f(g) = mu(-det g/c^2)|det g/c^2|^{s+1/2} F(oo)           if |c| >  |d|,
(c, d) = bottom row of g.  The new vector is the T(F_q)-fixed F (F(z) = mu^-1(z) on F_q^x, 0 at 0, oo).
A_m[y, x] = int_K f_{e_y}(k a_m) f~_{e_x}(k) dk is computed in closed form (cases on ord of the bottom-right
entry, see DERIVATION.md), and Phi(k1 a_m k2) = A_m(R(k2) v, R(k1^-1) v~)/<v, v~>.
   I_l = sum_m vol(K a_m K) E_{k1,k2 in GL2(F_q)} prod_i Phi_i(k1 a_m k2),  vol(K a_m K) = (q+1) q^(m-1).
Self-check: the unramified Steinberg Iwahori vector gives Phi(a_m) = q^-m (the Iwahori-Hecke value).
Usage: python3 local_triple_ps.py"""
import itertools, cmath
import numpy as np
from local_triple import characters

MMAX = 60


def setup(q):
    G, T, gm, mk = characters(q)
    pts = list(range(q)) + ['oo']
    idx = {p: i for i, p in enumerate(pts)}
    inv = lambda a: pow(a, -1, q)
    def ginv(g):
        a, b, c, d = g; D = inv((a * d - b * c) % q)
        return (d * D % q, -b * D % q, -c * D % q, a * D % q)
    reps = {z: (1, 0, z, 1) for z in range(q)}; reps['oo'] = (0, 1, 1, 0)
    return G, T, gm, mk, pts, idx, inv, ginv, reps


def model(q, mubar, s, u, setup_):
    """mubar: dict a -> value of mu on units (via reduction); returns translation operator and A_m."""
    G, T, gm, mk, pts, idx, inv, ginv, reps = setup_
    n = q + 1
    def evalf(F, h, mb):            # f(h) for h in GL2(F_q)
        a, b, c, d = h; det = (a * d - b * c) % q
        if d % q:
            return mb[det * inv(d * d % q) % q] * F[idx[c * inv(d) % q]]
        return mb[(-det) * inv(c * c % q) % q] * F[idx['oo']]
    def R(k, F, mb):                 # right translation by k in GL2(F_q)
        return np.array([evalf(F, gm(reps[z], k), mb) for z in pts])
    def A(m, mb):
        Am = np.zeros((n, n), dtype=complex)
        if m == 0:
            return np.eye(n) / n
        mu_m1 = mb[q - 1]            # mu(-1)
        sq1 = all(abs(mb[a] ** 2 - 1) < 1e-12 for a in range(1, q))
        e = s + 0.5
        for x in range(q):
            Am[idx[0], x] += u ** m * q ** (-m * e)
        if sq1:
            for j in range(1, m):
                Am[idx[0], idx['oo']] += mu_m1 * u ** (m - 2 * j) * q ** (-(m - 2 * j) * e) * (1 - 1 / q) * q ** (-(j - 1))
        for r in range(1, q):
            Am[idx[r], idx['oo']] += mu_m1 * mb[r] ** 2 * u ** (-m) * q ** (m * e) * (1 - 1 / q) * q ** (-(m - 1)) / (q - 1)
        Am[idx['oo'], idx['oo']] += u ** (-m) * q ** (m * e) * q ** (-m)
        return Am / n
    return R, A


def newvec(q, mubar_inv, idx):
    F = np.zeros(q + 1, dtype=complex)
    for z in range(1, q):
        F[idx[z]] = mubar_inv[z]
    return F


def rep(q, kind, e, u, S):
    G, T, gm, mk, pts, idx, inv, ginv, reps = S
    g0 = next(g for g in range(2, q) if all(pow(g, k, q) != 1 for k in range(1, q - 1)))
    lg = {pow(g0, k, q): k for k in range(q - 1)}
    if kind == 'St':
        mb = {a: (1 if pow(a, (q - 1) // 2, q) == 1 else -1) for a in range(1, q)}; s = 0.5
    elif kind == 'St1':
        mb = {a: 1 for a in range(1, q)}; s = 0.5
    else:
        mb = {a: cmath.exp(2j * cmath.pi * (lg[a] % e) / e) for a in range(1, q)}; s = 0.0
    mbi = {a: 1 / mb[a] for a in mb}
    R, A = model(q, mb, s, u, S)
    return R, A, mb, mbi


def integral(q, specs):
    S = setup(q)
    G, T, gm, mk, pts, idx, inv, ginv, reps = S
    mats = []
    for kind, e, u in specs:
        R, A, mb, mbi = rep(q, kind, e, u, S)
        v = newvec(q, mbi, idx); vt = newvec(q, mb, idx)     # v~ in Ind(mu^-1): F~ = mu(z)
        V = np.array([R(k, v, mb) for k in G])                # rows: R(k2) v
        W = np.array([R(ginv(k), vt, mbi) for k in G])        # rows: R(k1^-1) v~
        norm = (v @ vt) / (q + 1)
        mats.append((V, W, A, mb, norm))
    tot = 0
    for m in range(MMAX):
        prod = np.ones((len(G), len(G)), dtype=complex)
        for V, W, A, mb, norm in mats:
            prod *= (W @ A(m, mb).T @ V.T) / norm
        vol = 1 if m == 0 else (q + 1) * q ** (m - 1)
        tot += vol * prod.mean()
    return tot


def selfcheck_steinberg(q):
    S = setup(q); G, T, gm, mk, pts, idx, inv, ginv, reps = S
    R, A, mb, mbi = rep(q, 'St1', 0, 1, S)
    F = np.array([q if z == 0 else -1 for z in pts], dtype=complex)
    norm = (F @ F) / (q + 1)
    return [((F @ A(m, mb) @ F) / norm).real * q ** m for m in range(1, 6)]


if __name__ == '__main__':
    print('self-check (a) unramified St Iwahori: q^m Phi(a_m) =', np.round(selfcheck_steinberg(5), 10))
    u1 = (1 + 2j) / abs(1 + 2j); u2 = (2 + 1j) / abs(2 + 1j)
    cases = [(5, [('St', 0, 1)] * 3, 900, '(St x chi)^3, chi(varpi) = +1'),
             (5, [('St', 0, -1)] * 3, 900, '(St x chi)^3, chi(varpi) = -1'),
             # (St x chi, ps4, ps4): the class's partial L-polynomial 1 + 6T + 25T^2 = 1/L_l forces
             # w (u^2 + u^-2) = -6/5 with w = chi(varpi), u = mu(varpi) = alpha/sqrt5, alpha in Z[i], N(alpha) = 5.
             # Four (w, u) solutions; they form two pairs exchanged by u -> conj(u) (pi(mu, mu^-1) vs its
             # Galois conjugate with the same inertial type). The L-factor cannot tell them apart.
             (5, [('St', 0, 1), ('ps', 4, u1.conjugate()), ('ps', 4, u1.conjugate())], 50, 'w=+1, alpha=1-2i'),
             (5, [('St', 0, -1), ('ps', 4, u2), ('ps', 4, u2)], 50, 'w=-1, alpha=2+i'),
             (5, [('St', 0, 1), ('ps', 4, u1), ('ps', 4, u1)], 50, 'w=+1, alpha=1+2i (conjugate pair)'),
             (5, [('St', 0, -1), ('ps', 4, u2.conjugate()), ('ps', 4, u2.conjugate())], 50, 'w=-1, alpha=2-i (conjugate pair)')]
    for q, specs, X, note in cases:
        I = integral(q, specs)
        pred = X / (q ** 3 * (q - 1) ** 2 * (q + 1))
        print(f'q={q} {note:38s} I_l = {I.real:.10f}  from E\'s X: {pred:.10f}  match={abs(I.real - pred) < 1e-9}')
