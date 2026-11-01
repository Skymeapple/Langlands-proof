import ast, time
from g2lib import *
from jac3rank import sylow3_rank

def load2(path):
    allv=None; maxes=[]
    for line in open(path):
        tag, rest = line.split(" ",1)
        if tag=="ALL": allv={ (tuple(a),b,c,d) for a,b,c,d in ast.literal_eval(rest.strip())}
        else:
            size, rest = rest.split(" ",1); i=rest.rindex("]")
            maxes.append((int(size), rest[i+1:].strip(), {(tuple(a),b,c,d) for a,b,c,d in ast.literal_eval(rest[:i+1])}))
    return allv, maxes
ALL2, MAX2 = load2(os.path.join(os.path.dirname(os.path.abspath(__file__)),"maxsub2.txt"))

def frob_invariants(mm, N, primes=PRIMES, cps=None):
    """Exact invariants (charpoly mod 3, nu, dim ker(g-1), dim ker(g+1)) at good p>3."""
    out = {}
    F = pari(f"4*({mm[0]})+({mm[1]})^2")
    for p in primes:
        if p <= 3 or p in N: continue
        cp = cps[p] if cps and p in cps else charpoly(mm, p)
        P1 = sum(cp)                      # P(1) = #J(F_p)
        Pm1 = sum(c*(-1)**i for i,c in enumerate(cp))  # P(-1) = #J^twist(F_p)
        n = int(pari.znprimroot(p)) if False else None
        r1 = sylow3_rank(F, p, P1)
        nr = next(a for a in range(2,p) if pari.kronecker(a,p)==-1)
        r2 = sylow3_rank(F*nr, p, Pm1)
        if r1 is None or r2 is None: continue
        out[p] = (tuple(c % 3 for c in cp), p % 3, r1, r2)
    return out

def mod3_certify(invs):
    seen = set(invs.values())
    bad = seen - ALL2
    assert not bad, f"invariant not in GSp4(F3) table: {bad}"
    left = [(s,d) for s,d,M in MAX2 if seen <= M]
    return (not left), left

if __name__ == "__main__":
    for fh in [("-x^2-x","x^3+x^2+x+1"), ("x^5-x^4+x^3","1")]:
        t=time.time(); N,mm,bad=conductor_data(fh); cps=ap_list(mm,bad)
        iv=frob_invariants(mm,bad,cps=cps); print(N, len(iv), mod3_certify(iv), round(time.time()-t,1),"s")
