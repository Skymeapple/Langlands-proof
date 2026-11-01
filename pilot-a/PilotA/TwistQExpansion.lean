/-
Pilot A, milestone 3, step 4 (see `BLUEPRINT.md` §4): the q-expansion of the twisted cusp form.

If `f = Σ aₙ qⁿ` on `Γ₀(N)` and `χ` is a primitive real character mod `D` with Gauss sum `g ≠ 0`,
then `g⁻¹ · Σ_{a mod D} χ(a) f(τ + a/D) = Σ χ(n) aₙ qⁿ`.
-/
import PilotA.TwistOperator
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.ModularForms.QExpansion

set_option autoImplicit false

noncomputable section

namespace PilotA

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup ModularForm MatrixGroups
open UpperHalfPlane hiding I
open Matrix.GeneralLinearGroup (upperRightHom)
open Complex Function

open scoped Real

/-- Slashing by `T(x)` is translation by `x`. -/
lemma slash_upperRight_apply (f : ℍ → ℂ) (k : ℤ) (x : ℝ) (τ : ℍ) :
    (f ∣[k] upperRightHom x) τ = f (x +ᵥ τ) := by
  have h : upperRightHom x • τ = x +ᵥ τ := by
    ext
    simp [σ, num, denom, coe_vadd, UpperHalfPlane.coe_smul, add_comm]
  rw [slash_apply, h]
  simp [σ, denom, Matrix.GeneralLinearGroup.val_det_apply]

lemma qParam_vadd (x : ℝ) (τ : ℍ) :
    Periodic.qParam 1 ((x +ᵥ τ : ℍ) : ℂ) = cexp (2 * π * I * x) * Periodic.qParam 1 (τ : ℂ) := by
  simp only [Periodic.qParam, coe_vadd, ofReal_one, div_one]
  rw [← Complex.exp_add]; congr 1; ring

variable {D : ℕ} [NeZero D]

lemma exp_pow_eq_stdAddChar (a : ZMod D) (m : ℕ) :
    cexp (2 * π * I * ((((a.val : ℤ) : ℝ) / D : ℝ) : ℂ)) ^ m =
      (ZMod.stdAddChar.mulShift (m : ZMod D)) a := by
  rw [AddChar.mulShift_apply, ← Complex.exp_nat_mul, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  have : ((m : ZMod D) * a).val = ((m : ZMod D) * a).val := rfl
  rw [show ((m : ZMod D) * a) = (((m * a.val : ℕ) : ZMod D)) by push_cast; simp]
  rw [← ZMod.toCircle_apply, ZMod.toCircle_natCast]
  push_cast
  congr 1
  field_simp

/-- The coefficient identity behind the twist: `Σ_a χ(a) e(m a / D) = χ⁻¹(m) · g(χ)`. -/
lemma sum_char_exp (χ : DirichletCharacter ℂ D) (hχ : χ.IsPrimitive) (m : ℕ) :
    ∑ a : ZMod D, χ a * cexp (2 * π * I * ((((a.val : ℤ) : ℝ) / D : ℝ) : ℂ)) ^ m =
      χ⁻¹ (m : ZMod D) * gaussSum χ ZMod.stdAddChar := by
  rw [← gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ]
  simp only [gaussSum, exp_pow_eq_stdAddChar]

lemma one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

/-- The q-series of the twisted form: coefficient `m` is `g(χ) · χ⁻¹(m) · aₘ(f)`. -/
lemma hasSum_twistFun (N : ℕ) [NeZero N] (f : CuspForm (Gamma0 N) 2)
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsPrimitive) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (gaussSum χ ZMod.stdAddChar * χ⁻¹ (m : ZMod D) *
        (qExpansion 1 f).coeff m) • Periodic.qParam 1 (τ : ℂ) ^ m) (twistFun f χ τ) := by
  have : Fact (IsCusp OnePoint.infty (Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods_Gamma0 N)⟩
  have key : ∀ a : ZMod D, HasSum (fun m : ℕ ↦ χ a * ((qExpansion 1 f).coeff m *
      Periodic.qParam 1 (((((a.val : ℤ) : ℝ) / D : ℝ) +ᵥ τ : ℍ) : ℂ) ^ m))
      (χ a * f ((((a.val : ℤ) : ℝ) / D : ℝ) +ᵥ τ)) := fun a =>
    (ModularForm.hasSum_qExpansion (f := f) one_pos (one_mem_strictPeriods_Gamma0 N) _).mul_left _
  have hs := hasSum_sum (s := Finset.univ) (fun a _ => key a)
  have hval : twistFun f χ τ = ∑ a : ZMod D, χ a * f ((((a.val : ℤ) : ℝ) / D : ℝ) +ᵥ τ) := by
    simp only [twistFun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, slash_upperRight_apply]
  rw [hval]
  convert hs using 1
  funext m
  simp only [qParam_vadd, mul_pow, smul_eq_mul]
  rw [show ∀ g c q : ℂ, g * χ⁻¹ (m : ZMod D) * c * q = (χ⁻¹ (m : ZMod D) * g) * (c * q) from
    fun _ _ _ => by ring, ← sum_char_exp χ hχ m, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- Coefficients of the twisted cusp form. -/
lemma qExpansion_twistCuspForm_coeff (N : ℕ) [NeZero N] (f : CuspForm (Gamma0 N) 2)
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsPrimitive) (hχ2 : ∀ u : (ZMod D)ˣ, χ u ^ 2 = 1)
    (m : ℕ) :
    (qExpansion 1 (twistCuspForm N f χ hχ2)).coeff m =
      gaussSum χ ZMod.stdAddChar * χ⁻¹ (m : ZMod D) * (qExpansion 1 f).coeff m :=
  (ModularFormClass.qExpansion_coeff_unique (f := twistCuspForm N f χ hχ2)
    (c := fun m : ℕ ↦ gaussSum χ ZMod.stdAddChar * χ⁻¹ (m : ZMod D) * (qExpansion 1 f).coeff m)
    one_pos (one_mem_strictPeriods_Gamma0 _) (fun τ => hasSum_twistFun N f χ hχ τ) m).symm

/-- The Gauss sum of a primitive Dirichlet character (any modulus) is nonzero.
Proof by Fourier inversion: if `g = 0` then every `Σ_a χ(a) ψ(m a)` vanishes, hence `χ = 0`. -/
lemma gaussSum_ne_zero_of_isPrimitive (χ : DirichletCharacter ℂ D) (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar ≠ 0 := by
  intro h0
  have hψ := ZMod.isPrimitive_stdAddChar D
  have hm : ∀ m : ZMod D, ∑ a : ZMod D, χ a * ZMod.stdAddChar (m * a) = 0 := fun m => by
    have := gaussSum_mulShift_of_isPrimitive (e := ZMod.stdAddChar) hχ m
    rw [h0, mul_zero] at this
    simpa [gaussSum, AddChar.mulShift_apply] using this
  have hsum : ∑ m : ZMod D, ZMod.stdAddChar (-m) *
      ∑ a : ZMod D, χ a * ZMod.stdAddChar (m * a) = 0 := by
    simp [hm]
  have hswap : ∑ m : ZMod D, ZMod.stdAddChar (-m) *
      ∑ a : ZMod D, χ a * ZMod.stdAddChar (m * a) =
      ∑ a : ZMod D, χ a * ∑ m : ZMod D, ZMod.stdAddChar (m * (a - 1)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun m _ => ?_
    rw [show m * (a - 1) = -m + m * a by ring, AddChar.map_add_eq_mul]
    ring
  rw [hswap] at hsum
  simp only [AddChar.sum_mulShift _ hψ, sub_eq_zero, ZMod.card] at hsum
  push_cast at hsum
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    MulChar.map_one, one_mul] at hsum
  exact NeZero.ne D (by exact_mod_cast hsum)

end PilotA
