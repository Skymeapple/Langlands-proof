"""Ichino local integral at l for M = l^2 (conductor-2, depth-zero representations), computed exactly
from character tables of GL2(F_q), and compared with Pilot E's tabulated constants X.

For a depth-zero pi of conductor 2 with trivial central character, the K_0(l^2)-new vector v is fixed by
K_{v1}^+ (v1 = middle vertex of the path fixed by K_0(l^2)) and spans, under K_{v1}, the GL2(F_q)
representation tau = pi^{K^+}:
   sc (theta of F_{q^2}^x of order e | q+1, e>2):  tau = cuspidal sigma_theta  (dim q-1)
   ps (chi of F_q^x of order e | q-1, e>2):         tau = Ind_B(chi, chi^-1)    (dim q+1)
   St x chi (chi quadratic):                        tau = (chi o det) x St_q    (dim q)
and v spans tau^T for the diagonal torus T (image of K_0(l^2) in GL2(F_q)).  So on Z K_{v1}
   Phi(g) = <pi(g)v,v>/<v,v> = (1/|T|) sum_{t in T} chi_tau(g t).
A supercuspidal Phi vanishes off Z K_{v1}, so whenever one factor is sc,
   I_l = int_{PGL2(F_l)} prod Phi_i dg = (1/|GL2(F_q)|) sum_{g} prod Phi_i(g)     (vol PGL2(O) = 1).
Derived relation (DERIVATION.md section 2): with E's X = L^{(l)} prod<f,f>_D / (I^2 prod ||f||^2),
   I_l = 1 / (q^3 (q-1)^2 (q+1) X).
Usage: python3 local_triple.py"""
import itertools, cmath
from fractions import Fraction as Fr


def field(q):
    nu = next(c for c in range(2, q) if pow(c, (q - 1) // 2, q) == q - 1)
    els = [(a, b) for a in range(q) for b in range(q)]          # a + b s, s^2 = nu
    mul = lambda x, y: ((x[0] * y[0] + nu * x[1] * y[1]) % q, (x[0] * y[1] + x[1] * y[0]) % q)
    for g in els:
        if g == (0, 0):
            continue
        x, log = (1, 0), {}
        for k in range(q * q - 1):
            log[x] = k
            x = mul(x, g)
        if len(log) == q * q - 1:
            return nu, log, mul


def characters(q):
    nu, log, mul = field(q)
    N = q * q - 1
    G = [(a, b, c, d) for a, b, c, d in itertools.product(range(q), repeat=4) if (a * d - b * c) % q]

    def classify(g):
        a, b, c, d = g
        tr, det = (a + d) % q, (a * d - b * c) % q
        disc = (tr * tr - 4 * det) % q
        if b == 0 and c == 0 and a == d:
            return ('z', a)
        if disc == 0:
            return ('zu', tr * pow(2, -1, q) % q)
        if pow(disc, (q - 1) // 2, q) == 1:
            r = next(x for x in range(q) if x * x % q == disc)
            i2 = pow(2, -1, q)
            return ('split', (tr + r) * i2 % q, (tr - r) * i2 % q)
        # eigenvalue x = (tr + sqrt(disc))/2 in F_{q^2}, sqrt(disc) = y s with y^2 nu = disc
        y = next(y for y in range(q) if y * y * nu % q == disc)
        i2 = pow(2, -1, q)
        return ('ell', (tr * i2 % q, y * i2 % q))
    cls = {g: classify(g) for g in G}

    def sc(e):           # theta = character of F_{q^2}^x of order e, trivial on F_q^x
        assert (q + 1) % e == 0
        th = lambda x: cmath.exp(2j * cmath.pi * (q - 1) * log[x] / N * ((q + 1) // e) / ((q + 1) // e) * 1) if False else \
            cmath.exp(2j * cmath.pi * log[x] / e * 1 / 1) if False else cmath.exp(2j * cmath.pi * (log[x] % e) / e)
        def ch(g):
            c = cls[g]
            if c[0] == 'z':
                return (q - 1) * th((c[1], 0))
            if c[0] == 'zu':
                return -th((c[1], 0))
            if c[0] == 'split':
                return 0
            x = c[1]
            xq = (x[0], (-x[1]) % q)
            return -(th(x) + th(xq))
        return ch

    def logq(a):
        return log[(a, 0)] // (q + 1)       # F_q^x = <g^(q+1)>

    def ps(e):
        assert (q - 1) % e == 0
        mu = lambda a: cmath.exp(2j * cmath.pi * (logq(a) % e) / e)
        def ch(g):
            c = cls[g]
            if c[0] == 'z':
                return q + 1
            if c[0] == 'zu':
                return 1
            if c[0] == 'split':
                a, d = c[1], c[2]
                return mu(a) / mu(d) + mu(d) / mu(a)
            return 0
        return ch

    def stchi():
        chi = lambda a: 1 if pow(a, (q - 1) // 2, q) == 1 else -1
        def ch(g):
            a, b, c_, d = g
            c = cls[g]
            s = {'z': q, 'zu': 0, 'split': 1, 'ell': -1}[c[0]]
            return chi((a * d - b * c_) % q) * s
        return ch
    T = [(a, 0, 0, d) for a in range(1, q) for d in range(1, q)]
    gm = lambda g, h: ((g[0] * h[0] + g[1] * h[2]) % q, (g[0] * h[1] + g[1] * h[3]) % q,
                       (g[2] * h[0] + g[3] * h[2]) % q, (g[2] * h[1] + g[3] * h[3]) % q)
    return G, T, gm, dict(sc=sc, ps=ps, St=stchi)


def run(q, classes):
    G, T, gm, mk = characters(q)
    reps = {}
    for lab in {l for c in classes for l in c[0]}:
        if lab == 'Stxchi':
            reps[lab] = mk['St']()
        else:
            reps[lab] = mk[lab[:2]](int(lab[2:]))
    Phi = {}
    for lab, ch in reps.items():
        dimcheck = sum(ch(t) for t in T) / len(T)
        assert abs(dimcheck - 1) < 1e-9, (lab, dimcheck)   # tau^T is one-dimensional
        Phi[lab] = {g: sum(ch(gm(g, t)) for t in T) / len(T) for g in G}
    out = []
    for labs, X in classes:
        Il = sum(Phi[labs[0]][g] * Phi[labs[1]][g] * Phi[labs[2]][g] for g in G) / len(G)
        pred = Fr(1) / (q ** 3 * (q - 1) ** 2 * (q + 1) * X)
        approx = Fr(Il.real).limit_denominator(10 ** 6)
        out.append((labs, str(X), str(pred), str(approx), abs(Il.real - float(pred)) < 1e-9 and abs(Il.imag) < 1e-9))
    return out


if __name__ == '__main__':
    C5 = [(('Stxchi', 'Stxchi', 'sc6'), Fr(1, 900)), (('Stxchi', 'ps4', 'sc3'), Fr(1, 100)),
          (('Stxchi', 'sc3', 'sc3'), Fr(1, 1600)), (('ps4', 'ps4', 'sc6'), Fr(1, 500)),
          (('ps4', 'sc3', 'sc6'), Fr(1, 1000)), (('sc3', 'sc3', 'sc6'), Fr(1, 250)),
          (('sc6', 'sc6', 'sc6'), Fr(1, 2250))]
    C3 = [(('Stxchi', 'Stxchi', 'sc4'), Fr(1, 36)), (('sc4', 'sc4', 'sc4'), Fr(1, 108))]
    print('q  local types  E-constant X  I_l predicted from X  I_l computed  match')
    for q, C in ((3, C3), (5, C5)):
        for row in run(q, C):
            print(q, *row)
    # classes where E found I = 0: the local integral at l must vanish when eps_P = +1 (else P already kills it)
    Z5 = [('Stxchi', 'sc6', 'sc6'), ('Stxchi', 'sc3', 'sc6'), ('sc3', 'sc3', 'sc3'), ('sc3', 'sc6', 'sc6'),
          ('ps4', 'ps4', 'sc3'), ('ps4', 'sc3', 'sc3'), ('ps4', 'sc6', 'sc6'), ('Stxchi', 'ps4', 'sc6'),
          ('Stxchi', 'Stxchi', 'sc3')]
    Z3 = [('Stxchi', 'sc4', 'sc4')]
    for q, Z in ((3, Z3), (5, Z5)):
        G, T, gm, mk = characters(q)
        reps = {}
        for lab in {l for c in Z for l in c}:
            reps[lab] = mk['St']() if lab == 'Stxchi' else mk[lab[:2]](int(lab[2:]))
        Phi = {l: {g: sum(ch(gm(g, t)) for t in T) / len(T) for g in G} for l, ch in reps.items()}
        for labs in Z:
            Il = sum(Phi[labs[0]][g] * Phi[labs[1]][g] * Phi[labs[2]][g] for g in G) / len(G)
            print(q, labs, 'I_l =', round(abs(Il), 12))
