/-
Copyright (c) 2026 Liam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liam
-/
module

public import PilotD.AtkinLehner
public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.Algebra.DirectSum.Module

/-!
# Oldforms and newforms on `Γ₀(N)`

We define the old and new subspaces of `S_k(Γ₀(N))` and state the Atkin–Lehner decomposition
`S_k(Γ₀(N)) = ⨁_{M * d ∣ N} B_d (S_k^new(Γ₀(M)))`.

* For `M * d ∣ N` and `d ≠ 0`, the *level raising operator* `B_d : S_k(Γ₀(M)) → S_k(Γ₀(N))`
  is `(B_d f) τ = f (d τ)`. It is slashing by `!![d, 0; 0, 1]`, rescaled by `d ^ (1 - k)`.
* For `M ∣ N`, the *trace* `S_k(Γ₀(N)) → S_k(Γ₀(M))` is Mathlib's `CuspForm.trace`, the sum of
  the translates of `f` over `Γ₀(N) \ Γ₀(M)`.
* The *old subspace* is spanned by the images of `B_d` from levels `M < N`, `M * d ∣ N`.
* The *new subspace* is the common kernel of `Tr_{N / p}` and `Tr_{N / p} ∘ W_N` over primes
  `p ∣ N`.

The usual definition of the new subspace is the Petersson orthogonal complement of the old
subspace. The trace description used here is equivalent to it (Serre; see Li, *Newforms and
functional equations*, and Diamond–Shurman, §5.6), but that equivalence needs the Petersson
inner product on `S_k(Γ₀(N))`, which Mathlib does not have yet. It is not formalized here.

## Main definitions

* `CuspForm.levelRaise`: the operator `B_d`.
* `CuspForm.traceₗ`: the trace map, as a linear map.
* `CuspForm.oldSubspace`, `CuspForm.newSubspace`.
* `CuspForm.NewformDecomposition`: the statement of the Atkin–Lehner decomposition.

## Main results

* `CuspForm.levelRaise_apply`: `(B_d f) τ = f (d τ)`.
* `CuspForm.levelRaise_injective`.
* `CuspForm.newformDecomposition_one`: the decomposition at level `1`.

## TODO

* Prove `CuspForm.NewformDecomposition N k` for all `N`. This needs the Petersson inner product,
  or the Atkin–Lehner "main lemma" on forms whose `q`-expansion is supported on `n` sharing a
  factor with `N`.
-/

@[expose] public noncomputable section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup ModularForm MatrixGroups UpperHalfPlane
open ConjAct Pointwise

namespace CongruenceSubgroup

/-- `Γ₀(N) ≤ Γ₀(M)` when `M ∣ N`. -/
lemma Gamma0_le_Gamma0 {M N : ℕ} (h : M ∣ N) : Gamma0 N ≤ Gamma0 M := by
  intro γ hγ
  rw [Gamma0_mem] at hγ ⊢
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc]
  exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr h) _

lemma Gamma0_le_Gamma0_GL {M N : ℕ} (h : M ∣ N) :
    (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ≤ Gamma0 M :=
  Subgroup.map_mono (Gamma0_le_Gamma0 h)

/-- `Γ₀(N)` has finite index relative to `Γ₀(M)` when `N ≠ 0`. -/
instance isFiniteRelIndex_Gamma0 {M N : ℕ} [NeZero N] :
    (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).IsFiniteRelIndex (Gamma0 M) :=
  ⟨mt (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_le_range (mapGL ℝ) (Gamma0 M)))
    (Subgroup.relIndex_ne_zero (H := (Gamma0 N : Subgroup (GL (Fin 2) ℝ))) (K := 𝒮ℒ))⟩

/-- The level raising matrix `!![d, 0; 0, 1]`. -/
def levelRaiseMatrix (d : ℕ) [NeZero d] : GL (Fin 2) ℝ :=
  .mkOfDetNeZero !![(d : ℝ), 0; 0, 1] (by simp [Matrix.det_fin_two_of, NeZero.ne])

lemma coe_levelRaiseMatrix (d : ℕ) [NeZero d] :
    (levelRaiseMatrix d : Matrix (Fin 2) (Fin 2) ℝ) = !![(d : ℝ), 0; 0, 1] :=
  rfl

@[simp]
lemma det_levelRaiseMatrix (d : ℕ) [NeZero d] :
    (levelRaiseMatrix d : Matrix (Fin 2) (Fin 2) ℝ).det = d := by
  simp [coe_levelRaiseMatrix, Matrix.det_fin_two_of]

lemma det_levelRaiseMatrix_pos (d : ℕ) [NeZero d] : 0 < (levelRaiseMatrix d).det.val := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, det_levelRaiseMatrix]
  exact_mod_cast NeZero.pos d

private lemma mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    ((mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]

/-- Conjugation by `!![d, 0; 0, 1]` maps `Γ₀(N)` into `Γ₀(M)` when `M * d ∣ N`. -/
lemma Gamma0_le_conj_levelRaiseMatrix {M d N : ℕ} [NeZero d] (h : M * d ∣ N) :
    (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ≤
      toConjAct (levelRaiseMatrix d)⁻¹ • (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) := by
  intro x hx
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hx
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
  have hγ' := Gamma0_le_Gamma0 h hγ
  rw [Gamma0_mem] at hγ'
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ'
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rwa [Matrix.det_fin_two] at this
  let γ' : SL(2, ℤ) := ⟨!![γ 0 0, d * γ 0 1; M * c, γ 1 1], by
    rw [Matrix.det_fin_two_of]; rw [hc] at hdet; push_cast at hdet; linear_combination hdet⟩
  have hc' : ((γ 1 0 : ℤ) : ℝ) = M * d * c := by exact_mod_cast hc
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have key : levelRaiseMatrix d * mapGL ℝ γ = mapGL ℝ γ' * levelRaiseMatrix d := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        mapGL_apply] <;>
      simp [coe_levelRaiseMatrix, γ', hc']
    all_goals ring
  rw [key, mul_inv_cancel_right]
  exact Subgroup.mem_map_of_mem _ (by rw [Gamma0_mem]; simp [γ'])

end CongruenceSubgroup

namespace CuspForm

variable {k : ℤ}

/-! ### Level raising -/

/-- The **level raising operator** `B_d : S_k(Γ₀(M)) → S_k(Γ₀(N))`, `(B_d f) τ = f (d τ)`, for
`M * d ∣ N`. -/
def levelRaise (M d N : ℕ) [NeZero d] (h : M * d ∣ N) :
    CuspForm (Gamma0 M) k →ₗ[ℂ] CuspForm (Gamma0 N) k :=
  ((d : ℂ) ^ (1 - k)) • slashₗ (levelRaiseMatrix d)
    (det_levelRaiseMatrix_pos d)
    (Gamma0_le_conj_levelRaiseMatrix h)

/-- `!![d, 0; 0, 1] • τ = d τ`. -/
lemma coe_levelRaiseMatrix_smul (d : ℕ) [NeZero d] (τ : ℍ) :
    ((levelRaiseMatrix d • τ : ℍ) : ℂ) = d * τ := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  rw [UpperHalfPlane.coe_smul]
  simp [σ, num, denom, coe_levelRaiseMatrix, Matrix.det_fin_two_of, hd]

/-- `(B_d f) τ = f (d τ)`. -/
lemma levelRaise_apply (M d N : ℕ) [NeZero d] (h : M * d ∣ N) (f : CuspForm (Gamma0 M) k)
    (τ : ℍ) : levelRaise M d N h f τ = f (levelRaiseMatrix d • τ) := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  simp only [levelRaise, LinearMap.smul_apply, FunLike.coe_smul, Pi.smul_apply, coe_slashₗ,
    slash_apply, smul_eq_mul]
  have hdR : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hσ : σ (levelRaiseMatrix d) (f (levelRaiseMatrix d • τ)) = f (levelRaiseMatrix d • τ) := by
    simp [σ, coe_levelRaiseMatrix, Matrix.det_fin_two_of, hdR]
  have hden : denom (levelRaiseMatrix d) τ = 1 := by
    simp [denom, coe_levelRaiseMatrix]
  rw [hσ, hden, Matrix.GeneralLinearGroup.val_det_apply, det_levelRaiseMatrix, abs_of_pos hdR,
    one_zpow, mul_one, Complex.ofReal_natCast,
    mul_left_comm, ← zpow_add₀ hd, show 1 - k + (k - 1) = 0 by ring, zpow_zero, mul_one]

/-- `B_d` is injective. -/
theorem levelRaise_injective (M d N : ℕ) [NeZero d] (h : M * d ∣ N) :
    Function.Injective (levelRaise (k := k) M d N h) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  ext τ
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  let τ' : ℍ := ⟨(τ : ℂ) / d, by simpa using div_pos τ.im_pos hd⟩
  have hτ : levelRaiseMatrix d • τ' = τ := by
    ext
    rw [coe_levelRaiseMatrix_smul]
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    simp only [τ']
    field_simp
  have := congrArg (· τ') (congrArg DFunLike.coe hf)
  simp only [levelRaise_apply, hτ] at this
  simpa using this

/-! ### Traces -/

/-- The trace `S_k(Γ₀(N)) → S_k(Γ₀(M))`, as a linear map. When `M ∣ N` this is the sum of the
translates of `f` over `Γ₀(N) \ Γ₀(M)`. -/
def traceₗ (M N : ℕ) [NeZero N] : CuspForm (Gamma0 N) k →ₗ[ℂ] CuspForm (Gamma0 M) k :=
  { toFun f := CuspForm.trace _ f
    map_add' f f' := by
      ext τ
      simp only [CuspForm.coe_trace, FunLike.coe_add, Pi.add_apply, Finset.sum_apply,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      induction q using Quotient.inductionOn with
      | h r => simp [SlashAction.add_slash]
    map_smul' c f := by
      ext τ
      simp only [CuspForm.coe_trace, FunLike.coe_smul, Pi.smul_apply, Finset.sum_apply,
        smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      induction q using Quotient.inductionOn with
      | h r =>
        have hr := Subgroup.HasDetOne.det_eq (Subgroup.map_le_range _ _ r.2)
        simp [smul_slash, σ, Units.ext_iff.mp hr] }

/-! ### Old and new subspaces -/

/-- The **old subspace** of `S_k(Γ₀(N))`: the span of the images of `B_d : S_k(Γ₀(M)) →
S_k(Γ₀(N))` over `M * d ∣ N` with `M < N`. -/
def oldSubspace (N : ℕ) [NeZero N] (k : ℤ) : Submodule ℂ (CuspForm (Gamma0 N) k) :=
  ⨆ (Md : {Md : ℕ × ℕ // Md.1 * Md.2 ∣ N ∧ Md.1 < N}),
    haveI : NeZero Md.1.2 := ⟨right_ne_zero_of_mul (ne_zero_of_dvd_ne_zero (NeZero.ne N) Md.2.1)⟩
    LinearMap.range (levelRaise (k := k) Md.1.1 Md.1.2 N Md.2.1)

/-- The **new subspace** of `S_k(Γ₀(N))`: the forms `f` with `Tr_{N / p} f = 0` and
`Tr_{N / p} (f ∣ W_N) = 0` for every prime `p ∣ N`. -/
def newSubspace (N : ℕ) [NeZero N] (k : ℤ) : Submodule ℂ (CuspForm (Gamma0 N) k) :=
  ⨅ p ∈ N.primeFactors,
    LinearMap.ker (traceₗ (k := k) (N / p) N) ⊓ LinearMap.ker ((traceₗ (N / p) N).comp (fricke N))

/-- The pairs `(M, d)` with `M * d ∣ N`, indexing the Atkin–Lehner decomposition. -/
abbrev NewformIndex (N : ℕ) := {Md : ℕ × ℕ // Md.1 * Md.2 ∣ N}

/-- The summand `B_d (S_k^new(Γ₀(M)))` of `S_k(Γ₀(N))`. -/
def newformSummand (N : ℕ) [NeZero N] (k : ℤ) (i : NewformIndex N) :
    Submodule ℂ (CuspForm (Gamma0 N) k) :=
  haveI : NeZero i.1.1 := ⟨left_ne_zero_of_mul (ne_zero_of_dvd_ne_zero (NeZero.ne N) i.2)⟩
  haveI : NeZero i.1.2 := ⟨right_ne_zero_of_mul (ne_zero_of_dvd_ne_zero (NeZero.ne N) i.2)⟩
  (newSubspace i.1.1 k).map (levelRaise i.1.1 i.1.2 N i.2)

/-- **The Atkin–Lehner decomposition** (statement):
`S_k(Γ₀(N)) = ⨁_{M * d ∣ N} B_d (S_k^new(Γ₀(M)))`, as an internal direct sum. -/
def NewformDecomposition (N : ℕ) [NeZero N] (k : ℤ) : Prop :=
  DirectSum.IsInternal (newformSummand N k)

/-! ### Level one -/

lemma newSubspace_one : newSubspace 1 k = ⊤ := by
  simp [newSubspace]

lemma levelRaise_one_one_apply (f : CuspForm (Gamma0 1) k) :
    levelRaise 1 1 1 (one_dvd 1) f = f := by
  ext τ
  rw [levelRaise_apply]
  congr 1
  ext
  simp [coe_levelRaiseMatrix_smul]

/-- The Atkin–Lehner decomposition at level `1`: `S_k(Γ₀(1))` is all new. -/
theorem newformDecomposition_one : NewformDecomposition 1 k := by
  have hunique : ∀ i : NewformIndex 1, i = ⟨(1, 1), (one_dvd 1)⟩ := by
    rintro ⟨⟨M, d⟩, h⟩
    have := Nat.eq_one_of_mul_eq_one_right (Nat.dvd_one.mp h)
    have := Nat.eq_one_of_mul_eq_one_left (Nat.dvd_one.mp h)
    subst_vars
    rfl
  have : Subsingleton (NewformIndex 1) := ⟨fun i j ↦ (hunique i).trans (hunique j).symm⟩
  have htop : newformSummand 1 k ⟨(1, 1), one_dvd 1⟩ = ⊤ := by
    rw [eq_top_iff]
    intro f _
    exact ⟨f, by simp [newSubspace_one], levelRaise_one_one_apply f⟩
  rw [NewformDecomposition, DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨iSupIndep_subsingleton _, ?_⟩
  rw [eq_top_iff, ← htop]
  exact le_iSup (newformSummand 1 k) _

end CuspForm
