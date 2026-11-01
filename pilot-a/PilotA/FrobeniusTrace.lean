/-
Pilot A, target H6 (see `pilot-a/BLUEPRINT.md`).

The trace of Frobenius `a_p` does not depend on the integral equation: if two integral
Weierstrass equations over `ℤ` define isomorphic curves over `ℚ` and both have good reduction at
`p`, their reductions mod `p` have the same number of points, so `apOfModel` agrees.

References: Silverman, *The Arithmetic of Elliptic Curves*, VII.1.3(d) (the change of variables
between two equations that are both minimal at `p` is `p`-integral with unit `u`) and III.1.
-/
import PilotA.SemistableModel
import PilotA.Vendored.Def_FLTPrelim_Modularity
import Mathlib.NumberTheory.Padics.RingHoms

set_option autoImplicit false

namespace PilotA

open WeierstrassCurve

/-! ### Changes of variables over a field preserve the number of points -/

section Field

variable {F : Type*} [Field F]

lemma equation_smul_iff (W : WeierstrassCurve F) (C : VariableChange F) (x y : F) :
    (C • W).toAffine.Equation x y ↔
      W.toAffine.Equation (C.u ^ 2 * x + C.r) (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) := by
  rw [Affine.equation_iff', Affine.equation_iff']
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have key : (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) ^ 2
      + W.a₁ * (C.u ^ 2 * x + C.r) * (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t)
      + W.a₃ * (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t)
      - ((C.u ^ 2 * x + C.r) ^ 3 + W.a₂ * (C.u ^ 2 * x + C.r) ^ 2
        + W.a₄ * (C.u ^ 2 * x + C.r) + W.a₆)
      = (C.u : F) ^ 6 * (y ^ 2 + (C • W).a₁ * x * y + (C • W).a₃ * y
        - (x ^ 3 + (C • W).a₂ * x ^ 2 + (C • W).a₄ * x + (C • W).a₆)) := by
    simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      variableChange_a₆, Units.val_inv_eq_inv_val]
    field_simp
    ring
  rw [key]
  constructor
  · intro h; rw [h, mul_zero]
  · intro h; exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hu)

/-- The point map `(x, y) ↦ (u²x + r, u³y + u²sx + t)` from `C • W` to `W`. -/
def smulPointMap (W : WeierstrassCurve F) (C : VariableChange F) (hΔ : W.Δ ≠ 0) :
    (C • W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (C.u ^ 2 * x + C.r) (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t)
      ((Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp
        ((equation_smul_iff W C x y).mp h.1))

lemma smulPointMap_bijective (W : WeierstrassCurve F) (C : VariableChange F) (hΔ : W.Δ ≠ 0) :
    Function.Bijective (smulPointMap W C hΔ) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have hΔ' : (C • W).Δ ≠ 0 := by
    rw [variableChange_Δ]; exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hΔ
  constructor
  · rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) e
    · rfl
    · simp [smulPointMap] at e
    · simp [smulPointMap] at e
    · simp only [smulPointMap, Affine.Point.some.injEq] at e
      obtain ⟨e1, e2⟩ := e
      have hx : x = x' := by
        have : (C.u : F) ^ 2 * x = C.u ^ 2 * x' := by linear_combination e1
        exact mul_left_cancel₀ (pow_ne_zero _ hu) this
      subst hx
      have hy : y = y' := by
        have : (C.u : F) ^ 3 * y = C.u ^ 3 * y' := by linear_combination e2
        exact mul_left_cancel₀ (pow_ne_zero _ hu) this
      subst hy
      rfl
  · rintro (_ | ⟨X, Y, h⟩)
    · exact ⟨.zero, rfl⟩
    · set x : F := (X - C.r) / C.u ^ 2 with hx
      set y : F := (Y - C.u ^ 2 * C.s * x - C.t) / C.u ^ 3 with hy
      have eX : C.u ^ 2 * x + C.r = X := by rw [hx]; field_simp; ring
      have eY : C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t = Y := by rw [hy]; field_simp; ring
      have heq : (C • W).toAffine.Equation x y := by
        rw [equation_smul_iff, eX, eY]; exact h.1
      refine ⟨.some x y ((Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ').mp heq), ?_⟩
      simp only [smulPointMap, Affine.Point.some.injEq]
      exact ⟨eX, eY⟩

theorem card_smul (W : WeierstrassCurve F) (C : VariableChange F) (hΔ : W.Δ ≠ 0) :
    (C • W).card = W.card :=
  Nat.card_eq_of_bijective _ (smulPointMap_bijective W C hΔ)

end Field

/-! ### Reduction of a `p`-integral change of variables -/

section Reduction

variable {p : ℕ} [hp : Fact p.Prime]

/-- A `p`-integral rational as a `p`-adic integer. -/
noncomputable def toZp (q : ℚ) (h : padicNorm p q ≤ 1) : ℤ_[p] :=
  ⟨(q : ℚ_[p]), by rw [Padic.eq_padicNorm]; exact_mod_cast h⟩

lemma coe_toZp (q : ℚ) (h : padicNorm p q ≤ 1) : ((toZp q h : ℤ_[p]) : ℚ_[p]) = q := rfl

/-- **Model independence of `a_p`.** If two integral equations `W`, `W'` define the same curve over
`ℚ` (`C • W = W'` over `ℚ`) and both have good reduction at `p`, then `a_p(W) = a_p(W')`. -/
theorem apOfModel_eq_of_smul (W W' : WeierstrassCurve ℤ) (C : VariableChange ℚ)
    (hC : C • W.map (Int.castRingHom ℚ) = W'.map (Int.castRingHom ℚ))
    (hW : W.IsGoodPrimeFor p) (hW' : W'.IsGoodPrimeFor p) :
    W.apOfModel p = W'.apOfModel p := by
  set Wq := W.map (Int.castRingHom ℚ) with hWq
  have hinv := unit_pow_mul_inv_pow C.u
  -- `‖u‖ = 1`
  have nΔ : padicNorm p (W.Δ : ℚ) = 1 := (padicNorm.int_eq_one_iff _).mpr hW
  have nΔ' : padicNorm p (W'.Δ : ℚ) = 1 := (padicNorm.int_eq_one_iff _).mpr hW'
  have eΔ : (W.Δ : ℚ) = (C.u : ℚ) ^ 12 * (W'.Δ : ℚ) := by
    have h1 := congrArg WeierstrassCurve.Δ hC
    rw [map_Δ, eq_intCast, variableChange_Δ, hWq, map_Δ, eq_intCast] at h1
    rw [← h1, ← mul_assoc, hinv 12, one_mul]
  have hu1 : padicNorm p (C.u : ℚ) = 1 := by
    have := congrArg (padicNorm p) eΔ
    rw [padicNorm.mul, nΔ, nΔ', mul_one, n_pow_eq] at this
    exact (pow_eq_one_iff_of_nonneg (padicNorm.nonneg _) (by norm_num)).mp this.symm
  have hW'int : IsPIntegral p (C • Wq) := by rw [hC]; exact isPIntegral_map_int W'
  obtain ⟨hr, hs, ht⟩ := rst_le_one (isPIntegral_map_int W) C hW'int hu1.le
  -- lift `C` to `ℤ_[p]`
  have hu1' : ‖((C.u : ℚ) : ℚ_[p])‖ = 1 := by rw [Padic.eq_padicNorm]; exact_mod_cast hu1
  let Cz : VariableChange ℤ_[p] :=
    ⟨PadicInt.mkUnits hu1', toZp C.r hr, toZp C.s hs, toZp C.t ht⟩
  have hCz : Cz.map PadicInt.Coe.ringHom = C.map (Rat.castHom ℚ_[p]) := by
    ext
    · rfl
    · rfl
    · rfl
    · rfl
  have hcomp : (Rat.castHom ℚ_[p]).comp (Int.castRingHom ℚ) =
      PadicInt.Coe.ringHom.comp (Int.castRingHom ℤ_[p]) := RingHom.ext_int _ _
  have hZ : Cz • W.map (Int.castRingHom ℤ_[p]) = W'.map (Int.castRingHom ℤ_[p]) := by
    apply WeierstrassCurve.map_injective (f := PadicInt.Coe.ringHom) Subtype.val_injective
    show (Cz • W.map (Int.castRingHom ℤ_[p])).map PadicInt.Coe.ringHom =
      (W'.map (Int.castRingHom ℤ_[p])).map PadicInt.Coe.ringHom
    calc (Cz • W.map (Int.castRingHom ℤ_[p])).map PadicInt.Coe.ringHom
        = (Cz.map PadicInt.Coe.ringHom) •
            ((W.map (Int.castRingHom ℤ_[p])).map PadicInt.Coe.ringHom) :=
          (WeierstrassCurve.map_variableChange _ _ _).symm
      _ = (C.map (Rat.castHom ℚ_[p])) • (Wq.map (Rat.castHom ℚ_[p])) := by
          rw [hCz, hWq, map_map, map_map, hcomp]
      _ = (C • Wq).map (Rat.castHom ℚ_[p]) := WeierstrassCurve.map_variableChange _ _ _
      _ = (W'.map (Int.castRingHom ℤ_[p])).map PadicInt.Coe.ringHom := by
          rw [hC, map_map, map_map, hcomp]
  -- reduce mod `p`
  have hred : ∀ V : WeierstrassCurve ℤ,
      (V.map (Int.castRingHom ℤ_[p])).map PadicInt.toZMod = V.reductionMod p := by
    intro V
    rw [map_map, reductionMod]
    congr 1
    exact RingHom.ext_int _ _
  have hZp : (Cz.map PadicInt.toZMod) • W.reductionMod p = W'.reductionMod p := by
    rw [← hred, ← hred, WeierstrassCurve.map_variableChange, hZ]
  have hΔp : (W.reductionMod p).Δ ≠ 0 := by
    rw [reductionMod, map_Δ, eq_intCast]
    intro h0
    exact hW ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0)
  simp only [apOfModel, traceOfFrobenius]
  rw [← hZp, card_smul _ _ hΔp]

end Reduction

/-! ### Consequences for `IsModular` -/

/-- If `E` is modular, then **every** integral equation `W'` of `E` is matched by the eigenform at
all primes of good reduction for `W'` outside the level and outside one fixed nonzero integer
(the discriminant of the equation that witnessed modularity). So `IsModular` is independent of
the chosen equation, up to finitely many primes. -/
theorem IsModular.ap_eq_of_isIntegralModelOf {E : WeierstrassCurve ℚ} (hE : E.IsModular)
    (hEΔ : E.Δ ≠ 0) (W' : WeierstrassCurve ℤ) (hW' : W'.IsIntegralModelOf E) :
    ∃ (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (S : ℤ),
      0 < N ∧ S ≠ 0 ∧ f.IsNormalizedEigenform ∧
      ∀ p : ℕ, p.Prime → W'.IsGoodPrimeFor p → ¬ p ∣ N → ¬ (p : ℤ) ∣ S →
        ModularFormClass.qCoeff f p = (W'.apOfModel p : ℂ) := by
  obtain ⟨W₀, ⟨C₀, h₀⟩, N, hN, f, hf, hmatch⟩ := hE
  obtain ⟨C', h'⟩ := hW'
  have hΔ₀ : W₀.Δ ≠ 0 := by
    intro h0
    have := congrArg WeierstrassCurve.Δ h₀
    rw [map_Δ, h0, map_zero, variableChange_Δ] at this
    exact hEΔ ((mul_eq_zero.mp this).resolve_left (pow_ne_zero _ (Units.ne_zero _)))
  refine ⟨N, f, W₀.Δ, hN, hΔ₀, hf, ?_⟩
  intro p hp hgood hpN hpS
  haveI := Fact.mk hp
  have hC : (C' * C₀⁻¹) • W₀.map (Int.castRingHom ℚ) = W'.map (Int.castRingHom ℚ) := by
    rw [mul_smul, ← h₀, inv_smul_smul, h']
  rw [hmatch p hp hpS hpN, apOfModel_eq_of_smul W₀ W' _ hC hpS hgood]

end PilotA
