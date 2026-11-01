# Pilot B: which genus 2 curves over Q are known to be modular?

This folder tags genus 2 curves over Q by the published theorem (if any) that proves their
Jacobians modular, and settles some curves that no published theorem reaches directly.

Everything here is reproducible with `pip install cypari2 passagemath-gap` (PARI 2.17, GAP 4).

## Pipeline

| Step | Script | Output |
|---|---|---|
| Maximal subgroups of GSp4(F3) and the invariants their elements can have | `maxsub2.g` (GAP) | `maxsub2.txt` |
| Enumerate models y^2 + h y = f, h in {0,1}[x]_{<=3}, f coefficients in [-B,B], one per isogeny-class fingerprint | `enumerate.py B NMAX` | `classes_B1.jsonl`, `classes_B2*.jsonl` |
| Tag each class | `classify.py in out` | `tagged_*.jsonl` |
| Inventory table and statistics (deduped by isogeny fingerprint) | `summarize.py tagged...` | `data/inventory.csv`, `data/summary.json` |
| Unramified-at-2 test for semistable bad reduction (monodromy mod 3) | `semistable2.py` | none upgraded in this sample |
| Galois-side data for the conductor 349 target | `target349.py` | `data/target349.json` |
| Quadratic twists of Theorem A curves, with certificates | `twist_settle.py` | `twist_certs_*.json` |
| Independent re-check of every certificate | `verify_certificate.py certs.json` | `twist_verify_*.log` |

## What is rigorous

* Conductors and bad primes: PARI `genus2red`. PARI cannot always find the conductor exponent at 2
  (it reports -1); such classes are recorded with `N < 0` (odd part only). They are bad at 2.
* Frobenius polynomials: PARI `hyperellcharpoly`.
* **Mod 3 surjectivity** (Theorem A, hypothesis 1). Characteristic polynomials alone cannot do this:
  GSp4(F3) has only 15 of them and its maximal subgroup 2^{1+4}.A5.2 contains 13. So at a good
  prime p we use the finer invariant of g = rho_bar(Frob_p):
  (char poly mod 3, multiplier p mod 3, dim ker(g-1), dim ker(g+1)),
  where dim ker(g-1) is the 3-rank of J(F_p) and dim ker(g+1) is the 3-rank of the Jacobian of the
  quadratic twist over F_p. These ranks are computed exactly (`jac3rank.py`: Cantor's algorithm on a
  model with a rational Weierstrass point, generate the full Sylow 3-subgroup, whose order is known
  from the L-polynomial, then count its 3-torsion). The image is all of GSp4(F3) once each of the six
  conjugacy classes of maximal subgroups misses one of the observed invariants.
  Sanity checks: every observed invariant lies in GAP's list for GSp4(F3); 277.a (rational 15-torsion)
  is correctly found reducible mod 3; 249.a is certified surjective, matching LMFDB.
* Theorem A hypotheses 2 and 3: good reduction at 2 (sufficient for "unramified at 2"), Frob_2
  char poly mod 3 not (x^2 +- x + 2)^2, good ordinary reduction at 3, Frob_3 polynomial squarefree.
  Jacobians are principally polarized, so the polarization hypothesis holds.

## What is heuristic

The endomorphism labels NT-split / NT-RM / NT-other come from Frobenius polynomial shapes, not from a
certified endomorphism ring computation. A certified mod 3 surjective image does prove
End(J over Q-bar) = Z.

## Tags

* `A`: BCGP, Modularity theorems for abelian surfaces (arXiv:2502.20645), Theorem A, all hypotheses certified.
* `FS`: Faltings–Serre lists (BPPTVY 2019: 277, 353, 587; Berger–Klosin: 731).
* `NT-*`: heuristically non-typical; covered by older theorems or BCGP Thm 10.2.1 except "challenging" cases.
* `OPEN`: no theorem we can certify applies. Our test for "unramified at 2" is only sufficient, and
  BCGP allow some smaller mod 3 images (their Lemma 6.4.3, which we could not read), so a few OPEN
  classes might still be covered by Theorem A.

## Settled beyond the direct statement

If C satisfies Theorem A and d is in {-1, +-2, +-3, +-6}, the twist D = C^d has bad reduction at 2 or 3
from the ramified character, so Theorem A does not apply to D. But Jac(D) = Jac(C) (x) chi_d, so D is
modular. `twist_certs_B1.json` holds 4613 such curves (95 with conductor at most 10^6). Each one is
re-verified from scratch by `verify_certificate.py`. None of the 95 has minimal discriminant at most
10^6, so none of them is in the LMFDB genus 2 table.

## Current numbers (heights 1 and 2, conductor known and at most 10^6)

14,997 isogeny classes: Theorem A 3,330; Theorem A via a natural quadratic twist 3; Faltings-Serre 2;
heuristically non-typical 144; open 11,518. Most open classes fail one local condition: bad at 3 (3,808),
bad at 2 (1,675), non-ordinary at 3 (1,571), excluded Frob_2 polynomial (875).

## Next hard target: conductor 349

Poor-Yuen found a nonlift weight 2 paramodular form of level K(349). The surface has mod 2 image S5 with
quintic field of discriminant 2^4 * 349, the same residual type as 277 (proved by BPPTVY). Theorem A fails only
because Frob_2 mod 3 has char poly (x^2 + x + 2)^2. A Faltings-Serre proof along BPPTVY's lines needs the
Hecke eigenvalues of that form at primes up to roughly 43 (for 277 it was p <= 43). We could not find those
eigenvalues published, and LMFDB pages are behind a browser check from this environment.
`data/target349.json` has the Euler factors they must match.

## Round 3: the 365 open classes without a certified mod 3 image

`recert_mod3.py` (exact GAP + 3-rank test, primes up to 3000) and `reducibility_check.py` (char polys mod 3, primes < 1000).
Results in `data/round3_mod3.json`:

* None of the 365 becomes certified surjective, so none moves to Theorem A. The exact rerun with primes up to 3000 was done on 31 classes (stopped there: about 3 hours for all 365); all 31 stay inside the Klingen parabolic.
* 349 classes have every Frobenius char poly mod 3 compatible with both parabolics (a root in F3 and a split into quadratics). This is consistent with a reducible mod 3 image, like 277 (rational 15-torsion), but it is not a proof of reducibility. BCGP's introduction says the residual images their method allows are all absolutely irreducible.
* 16 classes are exactly excluded from the Klingen parabolic (and 6 also from the Siegel one), so their image may be irreducible inside SL(2,9):(C2 x C2) or (Q8 x Q8):(S3 x S3). Five of them (conductors 20923, 43771, 45125, 77803, 180625) satisfy every other Theorem A hypothesis. Whether they are covered depends only on BCGP Lemma 6.4.3, which we could not read.
