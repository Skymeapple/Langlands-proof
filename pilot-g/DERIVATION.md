# Pilot G: deriving the empirical period constants from local factors

Goal: explain the constants that Pilots E and C found numerically, using the Waldspurger and
Ichino(–Ikeda) formulas and explicit local integrals. Outcome labels: **derived** (a paper derivation
from a cited formula), **checked by computation** (exact rational arithmetic on stored data),
**numerical evidence**, **stalled**.

Sources, all quoted **from memory** because arXiv is blocked in this environment:
* [W] Waldspurger's toric period formula, in the form of Cai–Shu–Tian, *Explicit Gross–Zagier and
  Waldspurger formulae* (Algebra & Number Theory 2014), Thm 1.1. The function-field case is due to
  Chuang–Wei (*Waldspurger formula over function fields*).
* [I] Ichino, *Trilinear forms and the central values of triple product L-functions*
  (Duke 2008), Thm 1.1 and the remark on measures. The global constant is C/2³ for F×F×F.
* [IH] Ichino–Ikeda (GAFA 2010): only used to cross-check the shape of [W] (2^{-β}, L(1,η)).
* Iwahori–Hecke algebra matrix coefficients, and character tables of GL2(F_q): standard.

The one normalization I could not fix from memory is the global measure in [W]. Section 1.6
explains why the 603 matches with no free parameter support the conventions I used.

## 0. Setting and measures (F = F_q(t), genus 0)

* B is the definite quaternion algebra ramified at {P, ∞}, deg P = 1, G = PB^×, R is the Eichler
  order of level M, and n = PM with deg n = 3.
* μ0 is the product of local Haar measures with vol(PGL2(O_v)) = 1, vol(O_{B_v}^×/O_v^×) = 1 and
  vol(O_{K_v}^×/O_v^×) = 1 at every place, including ∞.
* vol_{μ0}([PB^×]) = 2/(q+1). Class number 1 plus O^× = F_{q²}^× leaves two points over ∞, each
  with stabiliser of order q+1. The Tamagawa measure (volume 2) is therefore (q+1)·μ0. This matches
  the local Tamagawa factors q³·ζ_F(2)^{-1}·Π_{v∈{P,∞}} (q_v−1)^{-1} = q+1.
* T = K^×\A_K^×/A^×. vol_{μ0}([T]) = 2h_K, from the index of K^×A^×U in A_K^× (it equals
  |Pic(K)/π*Pic(F)| = 2h_K). Since L(1,η) = P_K(1/q) = q^{-g_K}h_K, the [W] measure (volume
  2L(1,η)) is q^{-g_K}·μ0.
* Brandt side: φ ∈ π' is f_D on P^1(A/M)/(O^×/F_q^×). Its norm is
  ⟨φ,φ⟩_{μ0} = 2·ff/ψ(M), with ff = Σ f_D(i)²/#Stab_i and ψ(M) = [GL2(O_M) : R_M^×].
* All L-functions are complete (every place, ∞ included) and unitarily normalized. In Pilot E's
  variable T = q^{-s}, the centre of L(E,s) is T = 1/q, and L(1,π,Ad) = L(Sym²E, T = q^{-2}).

## 1. Gross / Waldspurger constant c (Pilot E): derived, and matched 603/603

[W] says P(φ)²/⟨φ,φ⟩ = ζ_F(2)·L(1/2,π_K)/(2L(1,π,Ad)) · Π_v α_v, where
α_v = [L(1,η_v)L(1,π_v,Ad)/(ζ_v(2)L(1/2,π_{K,v}))] · ∫_{T_v} ⟨π(t)φ_v,φ_v⟩/⟨φ_v,φ_v⟩ dt.

### 1.1 Global period
T(F)\T(A)/(T_∞ Π_{v<∞} O_{K_v}^×) = Pic(O_K), and O_K^× = F_q^×. Hence
P_{μ0}(φ) = vol(T_∞)·P_Pic = e_∞·P_Pic, where e_∞ = 2 if ∞ ramifies in K and 1 if it is inert
(T_∞/O^×_{K_∞} has order e_∞). P_Pic is Pilot E's sum over Pic(O_K), equal to the raw Gross point
sum divided by q+1.

### 1.2 Local integrals (μ0 measures)
| place | π_v | K_v | ∫ matrix coeff. | α_v |
|---|---|---|---|---|
| v ∤ nD0∞ | unramified | unramified | 1 | 1 |
| v ∣ D0 | unramified, a_v | ramified | 1 + a_v/(q_v+1) (ϖ_K moves the vertex by one step) | **1** |
| ℓ ∥ M | St⊗χ, χ(ϖ)=ε | split | Σ_k (ε/q)^{\|k\|} = (q+ε)/(q−ε) | (q_ℓ+1)/q_ℓ |
| ℓ² ∣ M (conductor 2) | L(s,π_ℓ)=1 | split | \|Z(½,W)\|²/⟨W,W⟩ = 1, since W_new = 1_{O^×} | L_ℓ(1,Ad)(q+1)/q |
| P | St⊗χ, JL = character | inert | 1 | (q−1)/q |
| ∞, inert in K | St | inert | 1 | (q−1)/q |
| ∞, ramified in K | St | ramified | vol(T_∞) = 2 | 2(q−1)/q |

The split-torus integrals use ∫_{F^×}⟨π(a(x))W,W⟩d^×x = |Z(½,W)|²/⟨W,W⟩ in the Whittaker
model. For St⊗χ, the edge computation and the Whittaker computation give the same value.

### 1.3 Assembly
Every ψ(M) cancels against the ℓ-factors, and each ℓ contributes 1/q_ℓ. With q_M = q² this gives

    P_Pic² / ff = |d_K|^{1/2} · L(E^{D0}, 1/q) / (κ · q² · L^{add}(1, π, Ad)),   κ = 2 (∞ ramified), 1 (∞ inert),

where q^{g_K−1} = |d_K|^{1/2}q^{-2}, and L^{add} drops the Euler factors at additive places
(they cancel against α_ℓ). The κ comes from e_∞² = 4 divided by the factor 2 in α_∞.

### 1.4 Verification (`gross_derived.py`)
L(1,Ad) is computed from the curves' Frobenius traces alone, as L(Sym²E,T) at T = q^{-2}.
* With squarefree conductor, L(Sym²E) is a polynomial of degree −6 + 2·4 = 2 (checked to T⁴).
* With one additive ℓ (conductor exponent 2), the complete L(Sym²) is 1. The partial product is
  exactly 1 − βT with β ∈ {1, q, −q}.
* **Result: the derived identity holds in 603 of 603 non-vanishing cases** (74 for q=3, 529 for
  q=5). The squares are compared exactly, and no constant is fitted.

### 1.5 Pilot E's c
Pilot E's identity reads L·ff·|d_K|^{1/2} = c·P_Pic²·‖f‖². Comparing it with 1.3 gives
c = κ·q²·L^{add}(1,Ad)/‖f‖². The computation finds **‖f‖²_Pet = q²·L^{add}(1,π,Ad) for all 164
newforms** (24 for q=3, 140 for q=5). Hence **c = κ = 2 (∞ ramified), 1 (∞ inert)**.
Status: derived from [W] plus local integrals, and checked by computation. One step is not derived
on paper: the Petersson identity ‖f‖² = q^{deg n − 1}L^{add}(1,Ad). That is the function-field
Rankin–Selberg normalization for E's primitive cochain, and here it is checked by computation only.

### 1.6 Why the measure conventions are trustworthy
A wrong global convention in [W] would show up as an extra factor such as L(1,η) (which depends on
D0), h_K, ζ_F(2) (which depends on q), or 2. None appears. The prediction holds across both K-types,
q = 3 and q = 5, deg D0 = 1, 2, 3, and squarefree and additive levels. Section 2 runs an independent
check with the same μ0 → Tamagawa conversion, and it reproduces 2^{ω(M)}q⁴.

## 2. Triple product constant 2^{ω(M)}·q⁴ (Pilot E): derived, and matched 33/33 (+116/116 zeros)

[I] says I(φ)²/Π⟨φ_i,φ_i⟩ = (C/8)·ζ_F(2)²·L(1/2,Π)/ΠL(1,π_i,Ad)·Π_v I_v^♮, where
I_v^♮ = ζ_v(2)^{-2}ΠL_v(1,Ad)/L_v(1/2,Π)·∫_{PB_v^×}ΠΦ_i dg, and C = q+1 for μ0. Also
I_{μ0}(φ) = 2I/ψ(M) and ⟨φ_i,φ_i⟩_{μ0} = 2ff_i/ψ(M).

* At P and ∞ (B ramified, π'_i = μ_i∘nrd): the integral is vol(PB_v^×) = 2 if Πμ_i = 1, otherwise
  0. That gives I^♮ = 2(1−1/q)², or 0 when ε_P = −1.
* At ℓ ∥ M (all Steinberg, Iwahori vectors): Φ_i(IwI) = χ_i(T_w)/q^{ℓ(w)} with T_s ↦ −1 and
  ω ↦ −ε_i. Summing over the extended affine Weyl group gives
  ∫ΠΦ_i = (1−ε)(q−1)/((q+1)(q²+1)), with ε = Πε_i. So I^♮ = 2(q_ℓ+1)/q_ℓ² if ε_ℓ = −1, and **0 if
  ε_ℓ = +1**.
* Assembly (ζ_F(2)(1−1/q)²(q+1) = q): I²/Πff = 2^{ω(M)}·L/(q²·ΠL(1,π_i,Ad)). Substituting
  L(1,Ad) = ‖f‖²/q² gives **L·Πff = I²·Π‖f‖²/(2^{ω(M)}q⁴)**, which is exactly Pilot E's empirical
  identity. The vanishing rule (ε_P = +1 and every ε_ℓ = −1) is derived as well.
* Verification (`triple_derived.py`, with L(1,Ad) from Frobenius traces): **33/33 allowed cases
  match. All 116/116 forbidden cases have I = 0.**

## 3. Triple products at levels M = ℓ² (Pilot E's 24 tabulated classes)

Conversion (same assembly, ψ(ℓ²) = q(q+1)): E's class constant X determines
**I_ℓ = 1/(q³(q−1)²(q+1)·X)**, where I_ℓ = ∫_{PGL2(F_ℓ)} ΠΦ_i dg. This uses the partial L at ℓ,
so the non-trivial local L-factors in 4 classes do not matter.

Local model. Every representation is depth zero with conductor 2. The new vector is fixed by
K^+_{v1}, where v1 is the middle vertex of the path that K_0(ℓ²) fixes. It spans the T(F_q)-fixed
line of τ = π^{K^+}: the cuspidal σ_θ (sc), Ind_B(χ, χ^{-1}) (ps), or (χ∘det)⊗St_q (St⊗χ). On
ZK_{v1}, Φ(g) = |T|^{-1}Σ_t χ_τ(gt).

* **Classes with a supercuspidal factor** (Φ_sc is supported on ZK_{v1}): I_ℓ is a finite
  character sum over GL2(F_q) (`local_triple.py`). **All 9 non-vanishing classes match E's X
  exactly**: q=3 (St⊗χ,St⊗χ,sc4) 1/36 and (sc4)³ 1/108; q=5 (St⊗χ,St⊗χ,sc6) 1/900,
  (St⊗χ,ps4,sc3) 1/100, (St⊗χ,sc3,sc3) 1/1600, (ps4,ps4,sc6) 1/500, (ps4,sc3,sc6) 1/1000,
  (sc3,sc3,sc6) 1/250, (sc6)³ 1/2250. **Every vanishing class with a supercuspidal factor has
  I_ℓ = 0** (10 classes). That includes (St⊗χ,sc6,sc6) with ε_P = +1 and L ≠ 0, which Pilot E
  could not explain.
* **(St⊗χ)³, q = 5** (non-compact, `local_triple_ps.py`): induced model on P^1(O) with closed-form
  kernels A_m, summed over K a_m K. The result I_ℓ = 3/40 matches X = 1/900 for both choices of
  χ(ϖ). The model is self-checked against the unramified Steinberg value Φ(a_m) = q^{-m}.
* **(St⊗χ, ps4, ps4), q = 5**: here the local representation is not determined by the Kodaira
  type. The class's partial L-polynomial 1 + 6T + 25T² forces χ(ϖ)(u² + u^{-2}) = −6/5, with
  u = μ(ϖ) = α/√5 and α ∈ Z[i] of norm 5. That leaves two Galois-conjugate candidates. One gives
  I_ℓ = 1/240, **exactly E's X = 1/50**. The other gives 25/240. Status: checked by computation for
  the matching candidate. **Open**: deciding which candidate the curve carries needs the local
  Langlands correspondence for this CM-type inertia character, for example by computing a twist by
  a quartic ramified character. That was not done.
* The classes with ε_P = −1 vanish because of the factor at P (Section 2). This is derived.

## 4. Pilot C's SO(5)×SO(4) constant 3/(8π³)·(p − ε_f): stalled (structural analysis only)

What can be said:
* By seesaw (SO(4)×SO(1) ⊂ SO(5) against Mp2 ⊃ Mp2 × Mp2), P(θ(h), g⊗g) = ⟨h, g·θ⟩. Here h is
  the weight-5/2 form that corresponds to f, g = θ_{SO(4)}(g⊗g) by Shimizu/Eichler, and θ is the
  unary theta series. This is the definite-form analogue of Ichino's 2005 pullback argument. It
  accounts for selection rule S1 (the theta lift from SO(4) vanishes on g1⊗g2 with g1 ≠ g2). It is consistent with
  the absence of any ‖g‖² or L(1,Ad g) term. This is a sketch, not checked here.
* (p − ε_f) is a local term at p. At p the quinary group is the non-quasi-split inner form
  PGU_2(D_p), and the SK local A-packet at p has two members, chosen by ε_f (f_p = St⊗χ with
  χ(p) = −ε_f in weight 4). The pair p−1 / p+1 has the typical shape of a ratio of parahoric volumes
  or a formal-degree ratio between those two members. **Hypothesis**, not derived.

Why it is not derived here:
1. No refined formula for this non-tempered case is available to me with reliable constants. The
   candidates are Qiu's *Periods of Saito–Kurokawa representations* (IMRN 2014) and the
   non-tempered GGP of Gan–Gross–Prasad 2020. I do not trust my memory of their global constants
   and archimedean factors, and arXiv is blocked.
2. The local factor at p needs the SK packet member's matrix coefficients on PGU_2(D_p), integrated
   over the SO(4) of the non-maximal lattice ⟨1⟩⊕(O,nrd). That is a self-contained but
   research-sized local computation.
3. The archimedean factor (3/(8π³) together with the weight-4 normalization of ‖f‖²) needs
   Rallis-inner-product constants for the theta lift from Mp2 to definite SO(5).

Concrete next step: with C's stored periods, compute the class-number-side quantity ⟨h, gθ⟩ from h
(a Brandt–Kohnen weight-5/2 form), and test whether |P|² = c·|⟨h,gθ⟩|² with c depending only on p.
That would split the constant into a Rallis piece and a Shimura-integral piece.
