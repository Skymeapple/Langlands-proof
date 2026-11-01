/-
Pilot A, target H2(a) (see `pilot-a/BLUEPRINT.md`): quadratic twists.

Proved here, from Mathlib only:
* `card_eq_sum_quadraticChar`: over a finite field of odd characteristic, a Weierstrass curve with
  `Δ ≠ 0` has `q + 1 + Σₓ χ(4x³ + b₂x² + 2b₄x + b₆)` points.
* `apOfModel_twist`: for the integral quadratic twist `twist W d`, `a_p(W^d) = (d/p) · a_p(W)` at
  every odd prime `p ∤ d` of good reduction for `W`.

Not proved (not in Mathlib): that the twist `Σ χ_d(n) aₙ qⁿ` of a weight-2 newform is again a
cusp form on some `Γ₀(M)` (Shimura, *Introduction to the arithmetic theory of automorphic
functions*, Prop. 3.64; Atkin–Li 1978). It enters `isModular_twist` as the explicit hypothesis
`TwistStatement`.
-/
import PilotA.FrobeniusTrace
import PilotA.Modularity
import Mathlib.NumberTheory.LegendreSymbol.Basic

set_option autoImplicit false

namespace PilotA

open WeierstrassCurve

/-! ### Counting points with the quadratic character -/

section Count

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The cubic `4x³ + b₂x² + 2b₄x + b₆` with `(2y + a₁x + a₃)² = f(x)` on the curve. -/
def cubicOf (W : WeierstrassCurve F) (x : F) : F :=
  4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆

lemma equation_iff_sq (W : WeierstrassCurve F) (hF : ringChar F ≠ 2) (x y : F) :
    W.toAffine.Equation x y ↔ (2 * y + W.a₁ * x + W.a₃) ^ 2 = cubicOf W x := by
  rw [Affine.equation_iff']
  have h4 : (4 : F) ≠ 0 := by
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have key : (4 : F) * (y ^ 2 + W.a₁ * x * y + W.a₃ * y
      - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))
      = (2 * y + W.a₁ * x + W.a₃) ^ 2 - cubicOf W x := by
    simp only [cubicOf, b₂, b₄, b₆]; ring
  constructor
  · intro h; rw [h, mul_zero] at key; exact (sub_eq_zero.mp key.symm)
  · intro h
    rw [h, sub_self] at key
    exact (mul_eq_zero.mp key).resolve_left h4

/-- Points of a curve with `Δ ≠ 0` are the point at infinity and the solutions of the equation. -/
def pointEquiv (W : WeierstrassCurve F) (hΔ : W.Δ ≠ 0) :
    W.toAffine.Point ≃ Option {xy : F × F // W.toAffine.Equation xy.1 xy.2} where
  toFun
    | .zero => none
    | .some x y h => some ⟨(x, y), h.1⟩
  invFun
    | none => .zero
    | some ⟨(x, y), h⟩ => .some x y ((Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp h)
  left_inv := by
    rintro (_ | ⟨x, y, h⟩) <;> rfl
  right_inv := by
    rintro (_ | ⟨⟨x, y⟩, h⟩) <;> rfl

theorem card_eq_sum_quadraticChar (W : WeierstrassCurve F) (hF : ringChar F ≠ 2)
    (hΔ : W.Δ ≠ 0) :
    (W.card : ℤ) = Fintype.card F + 1 + ∑ x : F, quadraticChar F (cubicOf W x) := by
  classical
  have e1 : W.card = Nat.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} + 1 := by
    rw [card, Nat.card_congr (pointEquiv W hΔ), Finite.card_option]
  have e2 : Nat.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} =
      ∑ x : F, Nat.card {y : F // W.toAffine.Equation x y} := by
    rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun x y => W.toAffine.Equation x y)), Nat.card_sigma]
  have e3 : ∀ x : F, (Nat.card {y : F // W.toAffine.Equation x y} : ℤ) =
      quadraticChar F (cubicOf W x) + 1 := by
    intro x
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    let e : F ≃ F := (Equiv.mulLeft₀ (2 : F) h2).trans (Equiv.addRight (W.a₁ * x + W.a₃))
    have he : ∀ y, W.toAffine.Equation x y ↔ (e y) ^ 2 = cubicOf W x := by
      intro y
      rw [equation_iff_sq W hF, add_assoc]
      rfl
    rw [Nat.card_congr (e.subtypeEquiv (q := fun z => z ^ 2 = cubicOf W x) he), ← quadraticChar_card_sqrts hF (cubicOf W x),
      ← Nat.card_eq_card_toFinset]
    rfl
  rw [e1, e2]
  push_cast
  rw [Finset.sum_congr rfl (fun x _ => e3 x), Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

theorem traceOfFrobenius_eq (W : WeierstrassCurve F) (hF : ringChar F ≠ 2) (hΔ : W.Δ ≠ 0) :
    W.traceOfFrobenius = -∑ x : F, quadraticChar F (cubicOf W x) := by
  rw [traceOfFrobenius, card_eq_sum_quadraticChar W hF hΔ, Nat.card_eq_fintype_card]
  ring

end Count

/-! ### The integral quadratic twist -/

/-- The quadratic twist of `W` by `d`, as the integral equation
`y² = x³ + d b₂ x² + 8 d² b₄ x + 16 d³ b₆` (isomorphic over `ℚ(√d)` to `W`). -/
def twist (W : WeierstrassCurve ℤ) (d : ℤ) : WeierstrassCurve ℤ :=
  ⟨0, d * W.b₂, 0, 8 * d ^ 2 * W.b₄, 16 * d ^ 3 * W.b₆⟩

lemma twist_Δ (W : WeierstrassCurve ℤ) (d : ℤ) : (twist W d).Δ = 2 ^ 12 * d ^ 6 * W.Δ := by
  simp only [twist, Δ, b₂, b₄, b₆, b₈]
  ring

section Prime

variable {p : ℕ} [hp : Fact p.Prime]

lemma ringChar_zmod_ne_two (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rwa [ZMod.ringChar_zmod_n]

/-- **Frobenius traces of quadratic twists.** `a_p(W^d) = (d/p) · a_p(W)` for odd `p ∤ d` of good
reduction for `W`. -/
theorem apOfModel_twist (W : WeierstrassCurve ℤ) (d : ℤ) (hp2 : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d)
    (hW : W.IsGoodPrimeFor p) :
    (twist W d).apOfModel p = legendreSym p d * W.apOfModel p := by
  have hF := ringChar_zmod_ne_two hp2
  set χ := quadraticChar (ZMod p)
  have hd0 : (d : ZMod p) ≠ 0 := fun h => hpd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero hF
  have hΔW : (W.reductionMod p).Δ ≠ 0 := by
    rw [reductionMod, map_Δ, eq_intCast]
    exact fun h => hW ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have hΔT : ((twist W d).reductionMod p).Δ ≠ 0 := by
    rw [reductionMod, map_Δ, eq_intCast, twist_Δ]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    rw [reductionMod, map_Δ, eq_intCast] at hΔW
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ hd0)) hΔW
  simp only [apOfModel]
  rw [traceOfFrobenius_eq _ hF hΔT, traceOfFrobenius_eq _ hF hΔW]
  -- relate the two cubics
  have h4 : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hcub : ∀ X : ZMod p, cubicOf ((twist W d).reductionMod p) (4 * X) =
      8 ^ 2 * (d : ZMod p) ^ 3 * cubicOf (W.reductionMod p) (X / d) := by
    intro X
    rw [cubicOf, cubicOf]
    simp only [reductionMod, map_b₂, map_b₄, map_b₆, eq_intCast]
    simp only [twist, b₂, b₄, b₆]
    push_cast
    field_simp
    ring
  have hsum1 : ∑ x : ZMod p, χ (cubicOf ((twist W d).reductionMod p) x) =
      ∑ X : ZMod p, χ (cubicOf ((twist W d).reductionMod p) (4 * X)) :=
    (Fintype.sum_equiv (Equiv.mulLeft₀ (4 : ZMod p) h4) _ _ (fun _ => rfl)).symm
  have hsum2 : ∑ X : ZMod p, χ (cubicOf (W.reductionMod p) (X / d)) =
      ∑ Y : ZMod p, χ (cubicOf (W.reductionMod p) Y) := by
    refine (Fintype.sum_equiv (Equiv.mulLeft₀ (d : ZMod p) hd0) _ _ (fun Y => ?_)).symm
    show χ (cubicOf (W.reductionMod p) Y) = χ (cubicOf (W.reductionMod p) ((d : ZMod p) * Y / d))
    rw [mul_div_cancel_left₀ _ hd0]
  have h8 : (8 : ZMod p) ≠ 0 := by
    have : (8 : ZMod p) = 2 * 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h2 h2) h2
  have hχ8 : χ 8 ^ 2 = 1 := quadraticChar_sq_one h8
  have hχd : χ d ^ 3 = χ d := by
    rcases quadraticChar_dichotomy hd0 with h | h <;> rw [h] <;> norm_num
  rw [hsum1]
  simp only [hcub, map_mul, map_pow, hχ8, one_mul]
  rw [← Finset.mul_sum, hχd, hsum2]
  simp only [legendreSym, χ]
  ring

end Prime

/-! ### Modularity of twists, given the twisting of eigenforms -/

/-- Twisting of weight-2 normalised eigenforms by quadratic characters (Shimura, Prop. 3.64;
Atkin–Li 1978). A classical theorem that is not in Mathlib; it is an explicit hypothesis here. -/
def TwistStatement : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform →
    ∀ d : ℤ, d ≠ 0 → ∃ M : ℕ, 0 < M ∧ N ∣ M ∧ ∃ g : CuspForm (CongruenceSubgroup.Gamma0 M) 2,
      g.IsNormalizedEigenform ∧ ∀ p : ℕ, (hp : p.Prime) → ¬ p ∣ N → ¬ (p : ℤ) ∣ 2 * d → ¬ p ∣ M →
        ModularFormClass.qCoeff g p = (@legendreSym p ⟨hp⟩ d : ℂ) * ModularFormClass.qCoeff f p

/-- If `W` is a modular integral equation, so is each of its quadratic twists (given
`TwistStatement`). -/
theorem isModularModel_twist (hT : TwistStatement) (W : WeierstrassCurve ℤ)
    (hW : W.IsModularModel) (d : ℤ) (hd : d ≠ 0) : (twist W d).IsModularModel := by
  obtain ⟨N, hN, f, hf, hmatch⟩ := hW
  obtain ⟨M, hM, hNM, g, hg, hgf⟩ := hT N hN f hf d hd
  refine ⟨M, hM, g, hg, ?_⟩
  intro p hp hgood hpM
  haveI := Fact.mk hp
  have hgood' : ¬ (p : ℤ) ∣ 2 ^ 12 * d ^ 6 * W.Δ := by
    have := hgood; rwa [IsGoodPrimeFor, twist_Δ] at this
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp2 : ¬ (p : ℤ) ∣ 2 := fun h => hgood' (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (dvd_pow h (by norm_num)) _) _)
  have hpd : ¬ (p : ℤ) ∣ d := fun h => hgood' (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_right (dvd_pow h (by norm_num)) _) _)
  have hpW : W.IsGoodPrimeFor p := fun h => hgood' (dvd_mul_of_dvd_right h _)
  have hp2' : p ≠ 2 := by
    rintro rfl; exact hp2 (by norm_num)
  have hpN : ¬ p ∣ N := fun h => hpM (dvd_trans h hNM)
  have h2d : ¬ (p : ℤ) ∣ 2 * d := by
    intro h
    rcases hpi.dvd_or_dvd h with h | h
    · exact hp2 h
    · exact hpd h
  rw [hgf p hp hpN h2d hpM, hmatch p hp hpW hpN, apOfModel_twist W d hp2' hpd hpW]
  push_cast
  ring

/-- **Quadratic twists of semistable curves are modular**, given Wiles's theorem (proved in the FLT
repo) and `TwistStatement` (classical, not in Mathlib). These twists have additive reduction at the
primes dividing `d`, so they lie outside the semistable case. -/
theorem isModular_twist_of_isSemistable (hWiles : WilesStatement) (hT : TwistStatement)
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) (d : ℤ) (hd : d ≠ 0) :
    ∃ W₀ : WeierstrassCurve ℤ, W₀.IsIntegralModelOf (W.map (Int.castRingHom ℚ)) ∧
      (twist W₀ d).IsModularModel := by
  obtain ⟨W₀, hW₀, hmod⟩ := hWiles W hΔ hW
  exact ⟨W₀, hW₀, isModularModel_twist hT W₀ hmod d hd⟩

end PilotA
