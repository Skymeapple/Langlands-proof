/-
Copyright (c) 2026 Liam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liam
-/
module

public import Mathlib.NumberTheory.ModularForms.Identities
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.MulChar.Basic

/-!
# Twisting cusp forms on `Γ₀(N)` by a quadratic character

For a function `f : ℍ → ℂ` and a multiplicative character `χ` of `ZMod D`, we define the
*twisting sum*
`twistSum k χ f = ∑ a : ZMod D, χ a • f ∣[k] T(a / D)`, where `T(x) = !![1, x; 0, 1]`,
so that `twistSum k χ f τ = ∑ a, χ a * f (τ + a / D)`.

If `f` is a cusp form of weight `k` on `Γ₀(N)` and `χ` is quadratic, then the twisting sum is a
cusp form of weight `k` on `Γ₀(N * D ^ 2)`. The key input is the matrix identity
`T(A / D) * γ = γ' * T(A' / D)` for `γ ∈ Γ₀(N * D ^ 2)`, with `γ' ∈ Γ₀(N)` and
`A' ≡ A * δ ^ 2 (mod D)`, where `δ` is the lower right entry of `γ`.

The `q`-expansion of the twist is computed in `PilotD.TwistQExpansion`.

## Main definitions

* `ModularForm.twistSum`: the twisting sum of a function `ℍ → ℂ`.
* `CuspForm.twistSum`: the twisting sum of a cusp form on `Γ₀(N)`, as a cusp form on
  `Γ₀(N * D ^ 2)`.

## Main results

* `ModularForm.twistSum_slash_eq`: invariance of the twisting sum under `Γ₀(N * D ^ 2)`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.64.
-/

@[expose] public noncomputable section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup ModularForm MatrixGroups UpperHalfPlane
open Matrix.GeneralLinearGroup (upperRightHom)

open scoped Manifold

namespace CongruenceSubgroup

lemma det_coe_SL2Z (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.det_coe
  rwa [Matrix.det_fin_two] at this

/-- The lower right entry of an element of `Γ₀(N * D)` is a unit modulo `D`. -/
lemma isUnit_coe_one_one_of_mem_Gamma0 {N D : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N * D)) :
    IsUnit ((γ 1 1 : ℤ) : ZMod D) := by
  rw [Gamma0_mem] at hγ
  obtain ⟨c₀, hc₀⟩ : ((N * D : ℕ) : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  have h := congrArg (Int.cast : ℤ → ZMod D) (det_coe_SL2Z γ)
  rw [hc₀] at h
  push_cast at h
  simp only [ZMod.natCast_self, mul_zero, zero_mul, sub_zero] at h
  exact .of_mul_eq_one_right _ h

end CongruenceSubgroup

namespace ModularForm

section Matrix

/-- `!![α, β; c, δ]` as an element of `SL(2, ℤ)`. -/
private def mkSL (α β c δ : ℤ) (h : α * δ - β * c = 1) : SL(2, ℤ) :=
  ⟨!![α, β; c, δ], by rw [Matrix.det_fin_two_of]; exact h⟩

private lemma eq_mkSL (γ : SL(2, ℤ)) :
    γ = mkSL (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (det_coe_SL2Z γ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The element `γ'` of `Γ₀(N)` with `T(A / D) * γ = γ' * T(A' / D)`, where
`γ = !![α, β; N * D ^ 2 * c₀, δ]` and `e * D = A * δ - A' * α`. -/
private def twistConj (α β δ A A' e N D c₀ : ℤ) (hdet : α * δ - β * (N * D ^ 2 * c₀) = 1)
    (he : e * D = A * δ - A' * α) : SL(2, ℤ) :=
  mkSL (α + A * N * D * c₀) (β + e - A * A' * N * c₀) (N * D ^ 2 * c₀) (δ - A' * N * D * c₀)
    (by linear_combination hdet - N * D * c₀ * he)

private lemma twistConj_mem (α β δ A A' e D c₀ : ℤ) (n : ℕ)
    (hdet : α * δ - β * (n * D ^ 2 * c₀) = 1) (he : e * D = A * δ - A' * α) :
    twistConj α β δ A A' e n D c₀ hdet he ∈ Gamma0 n := by
  rw [Gamma0_mem]
  simp [twistConj, mkSL]

private lemma mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    ((mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]

private lemma upperRightHom_mul_eq (α β δ A A' e N D c₀ : ℤ)
    (hdet : α * δ - β * (N * D ^ 2 * c₀) = 1) (he : e * D = A * δ - A' * α) (hD : (D : ℝ) ≠ 0) :
    upperRightHom ((A : ℝ) / D) * mapGL ℝ (mkSL α β (N * D ^ 2 * c₀) δ hdet) =
      mapGL ℝ (twistConj α β δ A A' e N D c₀ hdet he) * upperRightHom ((A' : ℝ) / D) := by
  have he' : (e : ℝ) * D = A * δ - A' * α := by exact_mod_cast he
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, mapGL_apply,
      Matrix.GeneralLinearGroup.upperRightHom_apply] <;>
    simp [twistConj, mkSL] <;> field_simp
  all_goals first | linear_combination -he' | linear_combination he' | ring1

end Matrix

variable {D : ℕ} [NeZero D] (k : ℤ)

/-- The translation `τ ↦ τ + a / D`, as an element of `GL(2, ℝ)`. -/
abbrev translateZMod (a : ZMod D) : GL (Fin 2) ℝ :=
  upperRightHom (((a.val : ℤ) : ℝ) / D)

/-- Moving one translate past an element of `Γ₀(N * D ^ 2)`. -/
lemma slash_translateZMod_slash {N : ℕ} {f : ℍ → ℂ} (hf : ∀ γ ∈ Gamma0 N, f ∣[k] γ = f)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (N * D ^ 2)) (a : ZMod D) :
    (f ∣[k] translateZMod a) ∣[k] γ = f ∣[k] translateZMod (a * (γ 1 1 : ZMod D) ^ 2) := by
  rw [Gamma0_mem] at hγ
  obtain ⟨c₀, hc₀⟩ : ((N * D ^ 2 : ℕ) : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  push_cast at hc₀
  set α := γ 0 0
  set β := γ 0 1
  set δ := γ 1 1
  set A : ℤ := (a.val : ℤ)
  set A' : ℤ := ((a * (δ : ZMod D) ^ 2).val : ℤ)
  have hdet : α * δ - β * ((N : ℤ) * (D : ℤ) ^ 2 * c₀) = 1 := by
    have := det_coe_SL2Z γ
    rwa [hc₀] at this
  have hdiv : (D : ℤ) ∣ A * δ - A' * α := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hA : ((A : ℤ) : ZMod D) = a := by simp [A]
    have hA' : ((A' : ℤ) : ZMod D) = a * (δ : ZMod D) ^ 2 := by simp [A']
    have hdet' : ((α : ℤ) : ZMod D) * δ = 1 := by
      have := congrArg (Int.cast : ℤ → ZMod D) hdet
      push_cast at this
      simpa [ZMod.natCast_self] using this
    push_cast
    rw [hA, hA']
    linear_combination (-(a * (δ : ZMod D))) * hdet'
  obtain ⟨e, he⟩ := hdiv
  have he' : e * (D : ℤ) = A * δ - A' * α := by rw [he]; ring
  have hD : ((D : ℤ) : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne D
  have hγeq : γ = mkSL α β ((N : ℤ) * (D : ℤ) ^ 2 * c₀) δ hdet := by
    rw [eq_mkSL γ]; congr 1
  rw [SL_slash, ← SlashAction.slash_mul]
  have hcast : (((a.val : ℤ) : ℝ) / D) = (A : ℝ) / ((D : ℤ) : ℝ) := by simp [A]
  have hcast' : ((((a * (γ 1 1 : ZMod D) ^ 2).val : ℤ) : ℝ) / D) =
      (A' : ℝ) / ((D : ℤ) : ℝ) := by
    simp [A', δ]
  simp only [translateZMod]
  rw [hcast, hcast']
  conv_lhs => rw [hγeq]
  rw [show ((mkSL α β ((N : ℤ) * (D : ℤ) ^ 2 * c₀) δ hdet : SL(2, ℤ)) : GL (Fin 2) ℝ) =
    mapGL ℝ (mkSL α β ((N : ℤ) * (D : ℤ) ^ 2 * c₀) δ hdet) from rfl,
    upperRightHom_mul_eq α β δ A A' e N D c₀ hdet he' hD, SlashAction.slash_mul]
  congr 1
  have hmem := hf _ (twistConj_mem α β δ A A' e D c₀ N hdet he')
  rwa [SL_slash] at hmem

/-- The twisting sum `τ ↦ ∑ a : ZMod D, χ a * f (τ + a / D)`, written with the weight `k` slash
action of the translations `T(a / D)`. -/
def twistSum (χ : MulChar (ZMod D) ℂ) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ a : ZMod D, χ a • f ∣[k] translateZMod a

/-- **Invariance of the twisting sum.** If `f` is invariant under `Γ₀(N)` in weight `k` and `χ`
is quadratic, then the twisting sum is invariant under `Γ₀(N * D ^ 2)`. -/
theorem twistSum_slash_eq {N : ℕ} {f : ℍ → ℂ} (hf : ∀ γ ∈ Gamma0 N, f ∣[k] γ = f)
    {χ : MulChar (ZMod D) ℂ} (hχ : χ.IsQuadratic) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 (N * D ^ 2)) :
    twistSum k χ f ∣[k] γ = twistSum k χ f := by
  obtain ⟨u, hu⟩ := isUnit_coe_one_one_of_mem_Gamma0 (N := N * D) (D := D)
    (by rwa [mul_assoc, ← pow_two])
  simp only [twistSum, SlashAction.sum_slash, SL_smul_slash,
    slash_translateZMod_slash k hf hγ]
  have hχu : χ ((u ^ 2 : (ZMod D)ˣ) : ZMod D) = 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow, ← MulChar.pow_apply' χ two_ne_zero, hχ.sq_eq_one,
      MulChar.one_apply_coe]
  refine Fintype.sum_equiv (Units.mulRight (u ^ 2)) _ _ fun a ↦ ?_
  change _ = χ (a * ↑(u ^ 2)) • _
  rw [map_mul, hχu, mul_one, ← hu]
  rfl

lemma mdifferentiable_twistSum {f : ℍ → ℂ} (hf : MDiff f) (χ : MulChar (ZMod D) ℂ) :
    MDiff (twistSum k χ f) :=
  .sum fun a _ ↦ (hf.slash k (translateZMod a)).const_smul (χ a)

private lemma upperRightHom_ratCast (x : ℚ) :
    (upperRightHom (x : ℚ)).map (Rat.castHom ℝ) = upperRightHom (x : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Translating a cusp of `SL(2, ℤ)` by a rational number gives a cusp of `SL(2, ℤ)`. -/
lemma isCusp_upperRightHom_ratCast_smul {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) (x : ℚ) :
    IsCusp (upperRightHom (x : ℝ) • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨q, rfl⟩ := hc
  refine ⟨upperRightHom x • q, ?_⟩
  classical
  have h := OnePoint.map_smul (Rat.castHom ℝ) (upperRightHom x) q
  rw [upperRightHom_ratCast] at h
  simpa using h

private lemma isZeroAt_sum {c : OnePoint ℝ} {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, c.IsZeroAt (F i) k) : c.IsZeroAt (∑ i ∈ s, F i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact fun g _ ↦ by rw [SlashAction.zero_slash]; exact Filter.zero_zeroAtFilter _
  | insert i t hi IH =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (IH fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

private lemma isZeroAt_const_smul {c : OnePoint ℝ} {F : ℍ → ℂ} (h : c.IsZeroAt F k) (z : ℂ) :
    c.IsZeroAt (z • F) k := fun g hg ↦ by
  rw [ModularForm.smul_slash]
  exact (h g hg).smul _

/-- The twisting sum of a cusp form on `Γ₀(N)` vanishes at every cusp of `SL(2, ℤ)`. -/
lemma isZeroAt_twistSum {N : ℕ} [NeZero N] (f : CuspForm (Gamma0 N) k)
    (χ : MulChar (ZMod D) ℂ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsZeroAt (twistSum k χ f) k := by
  refine isZeroAt_sum k _ _ fun a _ ↦ isZeroAt_const_smul k ?_ _
  rw [← OnePoint.IsZeroAt.smul_iff]
  apply CuspFormClass.zero_at_cusps f
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
  have e : (((a.val : ℤ) : ℝ) / D) = (((a.val : ℚ) / D : ℚ) : ℝ) := by push_cast; rfl
  simpa only [translateZMod, e] using isCusp_upperRightHom_ratCast_smul hc ((a.val : ℚ) / D)

end ModularForm

namespace CuspForm

variable {D : ℕ} [NeZero D] {k : ℤ} {N : ℕ} [NeZero N]

instance : NeZero (N * D ^ 2) := ⟨by simp [NeZero.ne]⟩

/-- The twisting sum `∑ a : ZMod D, χ a * f (τ + a / D)` of a cusp form `f` on `Γ₀(N)` by a
quadratic character `χ` of `ZMod D`, as a cusp form on `Γ₀(N * D ^ 2)`. -/
def twistSum (χ : MulChar (ZMod D) ℂ) (hχ : χ.IsQuadratic) (f : CuspForm (Gamma0 N) k) :
    CuspForm (Gamma0 (N * D ^ 2)) k where
  toFun := ModularForm.twistSum k χ f
  slash_action_eq' γ hγ := by
    obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.mp hγ
    have hf (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) : (f : ℍ → ℂ) ∣[k] γ = f := by
      rw [SL_slash]
      exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)
    have := ModularForm.twistSum_slash_eq k hf hχ hγ₀
    rw [SL_slash] at this
    exact this
  holo' := ModularForm.mdifferentiable_twistSum k (CuspFormClass.holo f) χ
  zero_at_cusps' hc :=
    ModularForm.isZeroAt_twistSum k f χ ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)

@[simp]
lemma coe_twistSum (χ : MulChar (ZMod D) ℂ) (hχ : χ.IsQuadratic) (f : CuspForm (Gamma0 N) k) :
    ⇑(twistSum χ hχ f) = ModularForm.twistSum k χ f :=
  rfl

end CuspForm
