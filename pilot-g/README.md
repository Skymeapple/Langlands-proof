# Pilot G: period constants from local Ichino–Ikeda / Waldspurger factors

Full derivation: [DERIVATION.md](DERIVATION.md). Data come from Pilot E (`../pilot-e/data`, PR #5)
and Pilot C (`pilot-c/so5`, PR #3). Requirements: Python 3, `pip install python-flint numpy`.

| Constant | Outcome | Evidence |
|---|---|---|
| Gross constant c = 2 (∞ ramified in K), 1 (∞ inert), over F_q(t) | **derived** from Waldspurger + explicit local integrals; the derived identity (in terms of L(1,Ad)) is **checked by computation in 603/603** non-vanishing cases, with no fitted constant | `gross_derived.py` |
| ‖f‖²_Pet = q²·L^{add}(1,π,Ad) for E's primitive cochains (the link between the formula and E's c) | **checked by computation** on 164/164 newforms; not derived on paper | `gross_derived.py` |
| Triple constant 2^{ω(M)}·q⁴ and the sign rule (ε_P=+1, ε_ℓ=−1) | **derived** from Ichino + Iwahori–Hecke local integrals; **checked by computation** 33/33, plus 116/116 forbidden cases with I = 0 | `triple_derived.py` |
| Triple constants at M = ℓ², classes with a supercuspidal factor | **derived** (finite character sums over GL2(F_q)): 9/9 non-vanishing classes match E's X exactly, and all 10 vanishing sc classes have local integral 0 (this explains (St⊗χ,sc6,sc6) with L ≠ 0) | `local_triple.py` |
| (St⊗χ)³ at M = ℓ², q = 5 | **derived** (induced model, non-compact sum): I_ℓ = 3/40 ⇔ X = 1/900 | `local_triple_ps.py` |
| (St⊗χ, ps4, ps4) at M = ℓ², q = 5 | **checked by computation, one local choice open**: the L-factor narrows the local representation to two Galois-conjugate candidates; one gives exactly X = 1/50, the other does not | `local_triple_ps.py` |
| ε_P = −1 classes at M = ℓ² (I = 0) | **derived** (local trilinear form at P vanishes) | DERIVATION.md §2 |
| Pilot C: 3/(8π³)·(p − ε_f) for SO(5)×SO(4) Saito–Kurokawa periods | **stalled**: seesaw reduction and a local-at-p hypothesis only; needs the non-tempered refined formula constants (Qiu / GGP 2020, unavailable offline) and a local computation on PGU_2(D_p) | DERIVATION.md §4 |

## Reproduce (from this folder, about 1 minute in total)

    python3 gross_derived.py 3 ../pilot-e/data/gross_q3.json ../pilot-e/data/match_q3.json
    python3 gross_derived.py 5 ../pilot-e/data/gross_q5.json ../pilot-e/data/match_q5.json
    python3 triple_derived.py 3 ../pilot-e/data/triple_q3.json ../pilot-e/data/match_q3.json
    python3 triple_derived.py 5 ../pilot-e/data/triple_q5.json ../pilot-e/data/match_q5.json
    python3 local_triple.py
    python3 local_triple_ps.py

Expected output is in `results.txt`.

## Assumptions (material)

* Waldspurger in the Cai–Shu–Tian form, and Ichino's global constant C/2³, are quoted from memory
  (arXiv is blocked). The measure conventions are pinned down by the 603 + 33 exact matches; see
  DERIVATION.md §1.6.
* Local representation types at ℓ come from Pilot E's Kodaira-type labels.
* The partial L-function at additive places is inferred from Frobenius traces up to the degree
  Pilot E stored (q=3: places of degree ≤ 4; q=5: degree ≤ 3). The degree bounds come from the
  conductor of Sym² (Grothendieck–Ogg–Shafarevich).
