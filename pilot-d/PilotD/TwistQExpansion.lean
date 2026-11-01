/-
Copyright (c) 2026 Liam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liam
-/
module

public import PilotD.GaussSum
public import PilotD.Twist
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The `q`-expansion of a twisted cusp form

Let `f = ∑ aₙ qⁿ` be a cusp form of weight `k` on `Γ₀(N)` and let `χ` be a primitive quadratic
Dirichlet character modulo `D`. Then the twisting sum `∑ a : ZMod D, χ a * f (τ + a / D)` has
`q`-expansion `∑ g(χ) χ(n) aₙ qⁿ`, where `g(χ)` is the Gauss sum of `χ`. Since `g(χ) ≠ 0`, the
normalized twist `f ⊗ χ = g(χ)⁻¹ • twistSum χ f` is a cusp form on `Γ₀(N * D ^ 2)` with
`q`-expansion `∑ χ(n) aₙ qⁿ`.

## Main definitions

* `CuspForm.twist`: the normalized twist `f ⊗ χ`.

## Main results

* `CuspForm.qExpansion_coeff_twistSum`: coefficients of the twisting sum.
* `CuspForm.qExpansion_coeff_twist`: `(f ⊗ χ)ₙ = χ(n) aₙ(f)`.
-/

@[expose] public noncomputable section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup ModularForm MatrixGroups
open UpperHalfPlane hiding I
open Matrix.GeneralLinearGroup (upperRightHom)
open Complex Function

open scoped Real

namespace ModularForm

/-- Slashing by `T(x) = !![1, x; 0, 1]` is translation by `x`. -/
lemma slash_upperRightHom_apply (f : ℍ → ℂ) (k : ℤ) (x : ℝ) (τ : ℍ) :
    (f ∣[k] upperRightHom x) τ = f (x +ᵥ τ) := by
  have h : upperRightHom x • τ = x +ᵥ τ := by
    ext
    simp [σ, num, denom, coe_vadd, UpperHalfPlane.coe_smul, add_comm]
  rw [slash_apply, h]
  simp [σ, denom, Matrix.GeneralLinearGroup.val_det_apply]

end ModularForm

namespace CuspForm

variable {D : ℕ} [NeZero D] {k : ℤ} {N : ℕ} [NeZero N]

private lemma qParam_vadd (x : ℝ) (τ : ℍ) :
    Periodic.qParam 1 ((x +ᵥ τ : ℍ) : ℂ) = cexp (2 * π * I * x) * Periodic.qParam 1 (τ : ℂ) := by
  simp only [Periodic.qParam, coe_vadd, ofReal_one, div_one]
  rw [← Complex.exp_add]
  congr 1
  ring

private lemma exp_pow_eq_stdAddChar (a : ZMod D) (m : ℕ) :
    cexp (2 * π * I * ((((a.val : ℤ) : ℝ) / D : ℝ) : ℂ)) ^ m =
      (ZMod.stdAddChar.mulShift (m : ZMod D)) a := by
  rw [AddChar.mulShift_apply, ← Complex.exp_nat_mul, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rw [show ((m : ZMod D) * a) = (((m * a.val : ℕ) : ZMod D)) by push_cast; simp]
  rw [← ZMod.toCircle_apply, ZMod.toCircle_natCast]
  push_cast
  congr 1
  field_simp

/-- `∑ a, χ(a) e(m a / D) = χ⁻¹(m) g(χ)` for a primitive Dirichlet character `χ`. -/
private lemma sum_mul_exp_pow (χ : DirichletCharacter ℂ D) (hχ : χ.IsPrimitive) (m : ℕ) :
    ∑ a : ZMod D, χ a * cexp (2 * π * I * ((((a.val : ℤ) : ℝ) / D : ℝ) : ℂ)) ^ m =
      χ⁻¹ (m : ZMod D) * gaussSum χ ZMod.stdAddChar := by
  rw [← gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ]
  simp only [gaussSum, exp_pow_eq_stdAddChar]

private lemma one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

omit [NeZero N] in
/-- The `q`-series of the twisting sum: the coefficient of `qᵐ` is `g(χ) χ⁻¹(m) aₘ(f)`. -/
lemma hasSum_twistSum (f : CuspForm (Gamma0 N) k) (χ : DirichletCharacter ℂ D)
    (hχ : χ.IsPrimitive) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (gaussSum χ ZMod.stdAddChar * χ⁻¹ (m : ZMod D) *
        (qExpansion 1 f).coeff m) • Periodic.qParam 1 (τ : ℂ) ^ m)
      (ModularForm.twistSum k χ f τ) := by
  have : Fact (IsCusp OnePoint.infty (Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods_Gamma0 N)⟩
  have key (a : ZMod D) : HasSum (fun m : ℕ ↦ χ a * ((qExpansion 1 f).coeff m *
      Periodic.qParam 1 (((((a.val : ℤ) : ℝ) / D : ℝ) +ᵥ τ : ℍ) : ℂ) ^ m))
      (χ a * f ((((a.val : ℤ) : ℝ) / D : ℝ) +ᵥ τ)) :=
    (ModularForm.hasSum_qExpansion (f := f) one_pos (one_mem_strictPeriods_Gamma0 N) _).mul_left _
  have hval : ModularForm.twistSum k χ f τ =
      ∑ a : ZMod D, χ a * f ((((a.val : ℤ) : ℝ) / D : ℝ) +ᵥ τ) := by
    simp only [ModularForm.twistSum, translateZMod, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      ModularForm.slash_upperRightHom_apply]
  rw [hval]
  convert hasSum_sum (s := Finset.univ) fun a _ ↦ key a using 1
  funext m
  simp only [qParam_vadd, mul_pow, smul_eq_mul]
  rw [show ∀ g c q : ℂ, g * χ⁻¹ (m : ZMod D) * c * q = (χ⁻¹ (m : ZMod D) * g) * (c * q) from
    fun _ _ _ ↦ by ring, ← sum_mul_exp_pow χ hχ m, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  ring

/-- Coefficients of the twisting sum of a cusp form by a primitive quadratic character. -/
lemma qExpansion_coeff_twistSum (f : CuspForm (Gamma0 N) k) (χ : DirichletCharacter ℂ D)
    (hχ : χ.IsPrimitive) (hχ₂ : χ.IsQuadratic) (m : ℕ) :
    (qExpansion 1 (twistSum χ hχ₂ f)).coeff m =
      gaussSum χ ZMod.stdAddChar * χ (m : ZMod D) * (qExpansion 1 f).coeff m := by
  have hs (τ : ℍ) := hasSum_twistSum f χ hχ τ
  simp only [hχ₂.inv] at hs
  exact (ModularFormClass.qExpansion_coeff_unique (f := twistSum χ hχ₂ f)
    (c := fun m : ℕ ↦ gaussSum χ ZMod.stdAddChar * χ (m : ZMod D) * (qExpansion 1 f).coeff m)
    one_pos (one_mem_strictPeriods_Gamma0 _) hs m).symm

/-- The normalized twist `f ⊗ χ = g(χ)⁻¹ • ∑ a, χ a * f (τ + a / D)` of a cusp form on `Γ₀(N)`
by a primitive quadratic character `χ` modulo `D`, as a cusp form on `Γ₀(N * D ^ 2)`. Its
`q`-expansion is `∑ χ(n) aₙ qⁿ` (see `CuspForm.qExpansion_coeff_twist`). -/
def twist (χ : DirichletCharacter ℂ D) (hχ₂ : χ.IsQuadratic) (f : CuspForm (Gamma0 N) k) :
    CuspForm (Gamma0 (N * D ^ 2)) k :=
  (gaussSum χ ZMod.stdAddChar)⁻¹ • twistSum χ hχ₂ f

/-- **Coefficients of the twist.** `aₙ(f ⊗ χ) = χ(n) aₙ(f)`. -/
theorem qExpansion_coeff_twist (f : CuspForm (Gamma0 N) k) (χ : DirichletCharacter ℂ D)
    (hχ : χ.IsPrimitive) (hχ₂ : χ.IsQuadratic) (m : ℕ) :
    (qExpansion 1 (twist χ hχ₂ f)).coeff m = χ (m : ZMod D) * (qExpansion 1 f).coeff m := by
  have : Fact (IsCusp OnePoint.infty (Gamma0 (N * D ^ 2) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods_Gamma0 _)⟩
  rw [twist, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma0 _), PowerSeries.coeff_smul,
    qExpansion_coeff_twistSum f χ hχ hχ₂,
    smul_eq_mul, ← mul_assoc, ← mul_assoc,
    inv_mul_cancel₀ (DirichletCharacter.gaussSum_stdAddChar_ne_zero hχ), one_mul]

end CuspForm
