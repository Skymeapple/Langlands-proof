/-
Copyright (c) 2026 Liam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liam
-/
module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# The Fricke (Atkin–Lehner) involution on `Γ₀(N)`

Let `W_N = !![0, -1 / √N; √N, 0] ∈ SL(2, ℝ)`. Conjugation by `W_N` preserves `Γ₀(N)`:
`W_N * !![a, b; N * c, d] = !![d, -c; -N * b, a] * W_N`. Hence slashing by `W_N` maps modular
(resp. cusp) forms of weight `k` on `Γ₀(N)` to modular (resp. cusp) forms of weight `k` on
`Γ₀(N)`. Since `W_N ^ 2 = -1 ∈ Γ₀(N)`, this *Fricke operator* is an involution. Explicitly,
`(f ∣ W_N) τ = (√N τ) ^ (-k) * f (-1 / (N τ))`.

We first set up, for any `g ∈ GL(2, ℝ)` with `0 < det g` and any `Γ' ≤ g⁻¹ Γ g`, the slash
operator `f ↦ f ∣[k] g` as a `ℂ`-linear map from forms on `Γ` to forms on `Γ'`. This is also
used for the level raising operators in `PilotD.Newforms`.

## Main definitions

* `ModularForm.restrict`, `CuspForm.restrict`: a form on `Γ` as a form on `Γ' ≤ Γ`.
* `ModularForm.slashₗ`, `CuspForm.slashₗ`: slashing by `g`, as a linear map.
* `CongruenceSubgroup.frickeMatrix`: the matrix `W_N`.
* `ModularForm.fricke`, `CuspForm.fricke`: the Fricke operator on `Γ₀(N)`.

## Main results

* `CongruenceSubgroup.conj_frickeMatrix_Gamma0`: `W_N` normalizes `Γ₀(N)`.
* `ModularForm.fricke_fricke`, `CuspForm.fricke_fricke`: the Fricke operator is an involution.
* `ModularForm.fricke_apply`: `(f ∣ W_N) τ = (√N τ) ^ (-k) * f (-1 / (N τ))`.

## References

* [A. O. L. Atkin and J. Lehner, *Hecke operators on `Γ₀(m)`*][atkinlehner1970]
-/

@[expose] public noncomputable section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup ModularForm MatrixGroups UpperHalfPlane
open ConjAct Pointwise

/-! ### Restriction and slashing as linear maps -/

namespace ModularForm

variable {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-- A modular form on `Γ`, regarded as a modular form on a subgroup `Γ' ≤ Γ`. -/
def restrict (h : Γ' ≤ Γ) (f : ModularForm Γ k) : ModularForm Γ' k where
  toFun := f
  slash_action_eq' γ hγ := SlashInvariantFormClass.slash_action_eq f γ (h hγ)
  holo' := ModularFormClass.holo f
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f (hc.mono h)

@[simp]
lemma coe_restrict (h : Γ' ≤ Γ) (f : ModularForm Γ k) : ⇑(restrict h f) = f :=
  rfl

variable [Γ.HasDetOne] [Γ'.HasDetOne]

/-- Slashing by `g ∈ GL(2, ℝ)` with `0 < det g`, as a `ℂ`-linear map from modular forms on `Γ` to
modular forms on any `Γ' ≤ g⁻¹ Γ g`. -/
def slashₗ (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) (h : Γ' ≤ toConjAct g⁻¹ • Γ) :
    ModularForm Γ k →ₗ[ℂ] ModularForm Γ' k where
  toFun f := restrict h (translate f g)
  map_add' f f' := by
    ext τ
    change (⇑(f + f') ∣[k] g) τ = (⇑f ∣[k] g) τ + (⇑f' ∣[k] g) τ
    rw [FunLike.coe_add, SlashAction.add_slash]
    rfl
  map_smul' c f := by
    ext τ
    change (⇑(c • f) ∣[k] g) τ = c * (⇑f ∣[k] g) τ
    have hg' : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
      rwa [← Matrix.GeneralLinearGroup.val_det_apply]
    rw [FunLike.coe_smul, smul_slash]
    simp [σ, hg']

@[simp]
lemma coe_slashₗ (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) (h : Γ' ≤ toConjAct g⁻¹ • Γ)
    (f : ModularForm Γ k) : ⇑(slashₗ g hg h f) = ⇑f ∣[k] g :=
  rfl

end ModularForm

namespace CuspForm

variable {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-- A cusp form on `Γ`, regarded as a cusp form on a subgroup `Γ' ≤ Γ`. -/
def restrict (h : Γ' ≤ Γ) (f : CuspForm Γ k) : CuspForm Γ' k where
  toFun := f
  slash_action_eq' γ hγ := SlashInvariantFormClass.slash_action_eq f γ (h hγ)
  holo' := CuspFormClass.holo f
  zero_at_cusps' hc := CuspFormClass.zero_at_cusps f (hc.mono h)

@[simp]
lemma coe_restrict (h : Γ' ≤ Γ) (f : CuspForm Γ k) : ⇑(restrict h f) = f :=
  rfl

variable [Γ.HasDetOne] [Γ'.HasDetOne]

/-- Slashing by `g ∈ GL(2, ℝ)` with `0 < det g`, as a `ℂ`-linear map from cusp forms on `Γ` to
cusp forms on any `Γ' ≤ g⁻¹ Γ g`. -/
def slashₗ (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) (h : Γ' ≤ toConjAct g⁻¹ • Γ) :
    CuspForm Γ k →ₗ[ℂ] CuspForm Γ' k where
  toFun f := restrict h (translate f g)
  map_add' f f' := by
    ext τ
    change (⇑(f + f') ∣[k] g) τ = (⇑f ∣[k] g) τ + (⇑f' ∣[k] g) τ
    rw [FunLike.coe_add, SlashAction.add_slash]
    rfl
  map_smul' c f := by
    ext τ
    change (⇑(c • f) ∣[k] g) τ = c * (⇑f ∣[k] g) τ
    have hg' : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
      rwa [← Matrix.GeneralLinearGroup.val_det_apply]
    rw [FunLike.coe_smul, smul_slash]
    simp [σ, hg']

@[simp]
lemma coe_slashₗ (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) (h : Γ' ≤ toConjAct g⁻¹ • Γ)
    (f : CuspForm Γ k) : ⇑(slashₗ g hg h f) = ⇑f ∣[k] g :=
  rfl

end CuspForm

/-! ### The Fricke matrix normalizes `Γ₀(N)` -/

namespace CongruenceSubgroup

variable (N : ℕ) [NeZero N]

private lemma sqrt_ne_zero' : √(N : ℝ) ≠ 0 :=
  Real.sqrt_ne_zero'.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))

/-- The Fricke matrix `W_N = !![0, -1 / √N; √N, 0]`, an element of `SL(2, ℝ)`. -/
def frickeMatrix : GL (Fin 2) ℝ :=
  .mkOfDetNeZero !![0, -(√(N : ℝ))⁻¹; √(N : ℝ), 0] (by
    simp [Matrix.det_fin_two_of, sqrt_ne_zero' N])

lemma coe_frickeMatrix :
    (frickeMatrix N : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -(√(N : ℝ))⁻¹; √(N : ℝ), 0] :=
  rfl

@[simp]
lemma det_frickeMatrix : (frickeMatrix N : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  simp [coe_frickeMatrix, Matrix.det_fin_two_of, sqrt_ne_zero' N]

lemma det_frickeMatrix_pos : 0 < (frickeMatrix N).det.val := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, det_frickeMatrix]
  exact one_pos

private lemma mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    ((mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]

/-- `W_N ^ 2 = -1`. -/
lemma frickeMatrix_mul_self : frickeMatrix N * frickeMatrix N = mapGL ℝ (-1 : SL(2, ℤ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mapGL_apply, coe_frickeMatrix, sqrt_ne_zero' N]

omit [NeZero N] in
lemma neg_one_mem_Gamma0 : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
  simp [Gamma0_mem]

/-- `W_N * !![a, b; N * c, d] = !![d, -c; -N * b, a] * W_N`. -/
lemma exists_frickeMatrix_mul_eq {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ∃ γ' ∈ Gamma0 N, frickeMatrix N * mapGL ℝ γ = mapGL ℝ γ' * frickeMatrix N := by
  rw [Gamma0_mem] at hγ
  obtain ⟨c, hc⟩ : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rwa [Matrix.det_fin_two] at this
  let γ' : SL(2, ℤ) := ⟨!![γ 1 1, -c; -(N * γ 0 1), γ 0 0], by
    rw [Matrix.det_fin_two_of]; rw [hc] at hdet; linear_combination hdet⟩
  refine ⟨γ', by rw [Gamma0_mem]; simp [γ'], ?_⟩
  have hN : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hs := sqrt_ne_zero' N
  have hc' : ((γ 1 0 : ℤ) : ℝ) = N * c := by exact_mod_cast hc
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      mapGL_apply] <;>
    simp [coe_frickeMatrix, γ', hc']
  all_goals field_simp
  all_goals simp only [Real.sq_sqrt (Nat.cast_nonneg _)]
  all_goals ring

/-- Conjugation by `W_N` maps `Γ₀(N)` into itself. -/
lemma Gamma0_le_conj_frickeMatrix :
    (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ≤ toConjAct (frickeMatrix N)⁻¹ • (Gamma0 N : _) := by
  intro x hx
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hx
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
  obtain ⟨γ', hγ', h⟩ := exists_frickeMatrix_mul_eq N hγ
  rw [h, mul_inv_cancel_right]
  exact Subgroup.mem_map_of_mem _ hγ'

/-- **`W_N` normalizes `Γ₀(N)`.** -/
theorem conj_frickeMatrix_Gamma0 :
    toConjAct (frickeMatrix N)⁻¹ • (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) = Gamma0 N := by
  refine le_antisymm (fun x hx ↦ ?_) (Gamma0_le_conj_frickeMatrix N)
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul] at hx
  have h2 := Gamma0_le_conj_frickeMatrix N hx
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul] at h2
  have hm : mapGL ℝ (-1 : SL(2, ℤ)) ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.mem_map_of_mem _ (neg_one_mem_Gamma0 N)
  have key : x = (mapGL ℝ (-1 : SL(2, ℤ)))⁻¹ *
      (frickeMatrix N * (frickeMatrix N * x * (frickeMatrix N)⁻¹) * (frickeMatrix N)⁻¹) *
      mapGL ℝ (-1 : SL(2, ℤ)) := by
    rw [← frickeMatrix_mul_self N]
    group
  rw [key]
  exact mul_mem (mul_mem (inv_mem hm) h2) hm

end CongruenceSubgroup

/-! ### The Fricke operator -/

namespace ModularForm

variable (N : ℕ) [NeZero N] {k : ℤ}

/-- The **Fricke operator** `f ↦ f ∣[k] W_N` on modular forms of weight `k` on `Γ₀(N)`. -/
def fricke : ModularForm (Gamma0 N) k →ₗ[ℂ] ModularForm (Gamma0 N) k :=
  slashₗ (frickeMatrix N) (det_frickeMatrix_pos N)
    (Gamma0_le_conj_frickeMatrix N)

lemma coe_fricke (f : ModularForm (Gamma0 N) k) : ⇑(fricke N f) = ⇑f ∣[k] frickeMatrix N :=
  rfl

/-- **The Fricke operator is an involution.** -/
@[simp]
theorem fricke_fricke (f : ModularForm (Gamma0 N) k) : fricke N (fricke N f) = f := by
  ext τ
  rw [coe_fricke, coe_fricke, ← SlashAction.slash_mul, frickeMatrix_mul_self,
    SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ (neg_one_mem_Gamma0 N))]

lemma fricke_involutive : Function.Involutive (fricke N (k := k)) :=
  fricke_fricke N

/-- `(f ∣ W_N) τ = (√N τ) ^ (-k) * f (W_N • τ)`. -/
lemma fricke_apply (f : ModularForm (Gamma0 N) k) (τ : ℍ) :
    fricke N f τ = (√(N : ℝ) * (τ : ℂ)) ^ (-k) * f (frickeMatrix N • τ) := by
  rw [coe_fricke, slash_apply]
  have hs := sqrt_ne_zero' N
  simp [σ, denom, coe_frickeMatrix, hs]
  ring

/-- `W_N • τ = -1 / (N τ)`. -/
lemma coe_frickeMatrix_smul (τ : ℍ) :
    ((frickeMatrix N • τ : ℍ) : ℂ) = -1 / (N * τ) := by
  have hs : (√(N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sqrt_ne_zero' N
  have hN : (√(N : ℝ) : ℂ) * √(N : ℝ) = N := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hsR := sqrt_ne_zero' N
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [UpperHalfPlane.coe_smul]
  simp [σ, num, denom, coe_frickeMatrix, hsR]
  field_simp
  linear_combination hN

end ModularForm

namespace CuspForm

variable (N : ℕ) [NeZero N] {k : ℤ}

/-- The **Fricke operator** `f ↦ f ∣[k] W_N` on cusp forms of weight `k` on `Γ₀(N)`. -/
def fricke : CuspForm (Gamma0 N) k →ₗ[ℂ] CuspForm (Gamma0 N) k :=
  slashₗ (frickeMatrix N) (det_frickeMatrix_pos N)
    (Gamma0_le_conj_frickeMatrix N)

lemma coe_fricke (f : CuspForm (Gamma0 N) k) : ⇑(fricke N f) = ⇑f ∣[k] frickeMatrix N :=
  rfl

/-- **The Fricke operator is an involution.** -/
@[simp]
theorem fricke_fricke (f : CuspForm (Gamma0 N) k) : fricke N (fricke N f) = f := by
  ext τ
  rw [coe_fricke, coe_fricke, ← SlashAction.slash_mul, frickeMatrix_mul_self,
    SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ (neg_one_mem_Gamma0 N))]

lemma fricke_involutive : Function.Involutive (fricke N (k := k)) :=
  fricke_fricke N

end CuspForm
