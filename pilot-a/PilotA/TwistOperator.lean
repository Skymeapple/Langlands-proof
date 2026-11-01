/-
Pilot A, milestone 3, step 3 (see `BLUEPRINT.md` §4): the matrix identity behind the invariance of
a twisted cusp form, and the invariance itself.

For `γ = [[α, β], [c, δ]] ∈ Γ₀(N D²)` and an integer `A`, with `A' ≡ A δ² (mod D)`:
`T(A/D) · γ = γ' · T(A'/D)` with `γ' ∈ Γ₀(N)`, where `T(x) = [[1, x], [0, 1]]`.
-/
import Mathlib.NumberTheory.ModularForms.Identities
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

set_option autoImplicit false

noncomputable section

open scoped Manifold

namespace PilotA

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup ModularForm MatrixGroups UpperHalfPlane
open Matrix.GeneralLinearGroup (upperRightHom)

/-- `[[α, β], [c, δ]]` as an element of `SL(2, ℤ)`. -/
def mkSL (α β c δ : ℤ) (h : α * δ - β * c = 1) : SL(2, ℤ) :=
  ⟨!![α, β; c, δ], by rw [Matrix.det_fin_two_of]; exact h⟩

lemma det_SL2 (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.det_coe
  rwa [Matrix.det_fin_two] at this

lemma eq_mkSL (γ : SL(2, ℤ)) : γ = mkSL (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (det_SL2 γ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The explicit `γ'` with `T(A/D) · γ = γ' · T(A'/D)`, where `c = N D² c₀` and
`e D = A δ - A' α`. -/
def gammaPrime (α β δ A A' e N D c₀ : ℤ) (hdet : α * δ - β * (N * D ^ 2 * c₀) = 1)
    (he : e * D = A * δ - A' * α) : SL(2, ℤ) :=
  mkSL (α + A * N * D * c₀) (β + e - A * A' * N * c₀) (N * D ^ 2 * c₀) (δ - A' * N * D * c₀)
    (by linear_combination hdet - N * D * c₀ * he)

lemma gammaPrime_mem (α β δ A A' e D c₀ : ℤ) (n : ℕ)
    (hdet : α * δ - β * (n * D ^ 2 * c₀) = 1) (he : e * D = A * δ - A' * α) :
    gammaPrime α β δ A A' e n D c₀ hdet he ∈ Gamma0 n := by
  rw [Gamma0_mem]
  simp [gammaPrime, mkSL]

lemma mapGL_apply' (g : SL(2, ℤ)) (i j : Fin 2) :
    ((mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]

lemma upperRight_mul_eq (α β δ A A' e N D c₀ : ℤ) (hdet : α * δ - β * (N * D ^ 2 * c₀) = 1)
    (he : e * D = A * δ - A' * α) (hD : (D : ℝ) ≠ 0) :
    upperRightHom ((A : ℝ) / D) * mapGL ℝ (mkSL α β (N * D ^ 2 * c₀) δ hdet) =
      mapGL ℝ (gammaPrime α β δ A A' e N D c₀ hdet he) * upperRightHom ((A' : ℝ) / D) := by
  have he' : (e : ℝ) * D = A * δ - A' * α := by exact_mod_cast he
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, mapGL_apply',
      Matrix.GeneralLinearGroup.upperRightHom_apply] <;>
    simp [gammaPrime, mkSL] <;> field_simp
  all_goals first | linear_combination -he' | linear_combination he' | ring1

/-! ### The twist operator and its invariance -/

variable {D : ℕ} [NeZero D]

/-- `Σ_{a mod D} χ(a) · f(τ + a/D)`, written with the slash action of `T(a/D)`. -/
def twistFun (f : ℍ → ℂ) (χ : MulChar (ZMod D) ℂ) : ℍ → ℂ :=
  ∑ a : ZMod D, χ a • (f ∣[(2 : ℤ)] upperRightHom (((a.val : ℤ) : ℝ) / D))

/-- One translate, moved past `γ ∈ Γ₀(N D²)`. -/
lemma translate_slash (N : ℕ) (f : ℍ → ℂ) (hf : ∀ γ ∈ Gamma0 N, f ∣[(2 : ℤ)] γ = f)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 (N * D ^ 2)) (a : ZMod D) :
    (f ∣[(2 : ℤ)] upperRightHom (((a.val : ℤ) : ℝ) / D)) ∣[(2 : ℤ)] γ =
      f ∣[(2 : ℤ)] upperRightHom ((((a * (γ 1 1 : ZMod D) ^ 2).val : ℤ) : ℝ) / D) := by
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
    have := det_SL2 γ; rw [hc₀] at this; exact this
  -- `D ∣ A δ - A' α`
  have hdiv : (D : ℤ) ∣ A * δ - A' * α := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hA : ((A : ℤ) : ZMod D) = a := by simp [A]
    have hA' : ((A' : ℤ) : ZMod D) = a * (δ : ZMod D) ^ 2 := by simp [A']
    have hdet' : ((α : ℤ) : ZMod D) * δ = 1 := by
      have := congrArg (Int.cast : ℤ → ZMod D) hdet
      push_cast at this
      have hD0 : ((D : ℤ) : ZMod D) = 0 := by simp
      rw [show ((D : ℤ) : ZMod D) = (D : ZMod D) by simp] at hD0
      simpa [ZMod.natCast_self] using this
    push_cast
    rw [hA, hA']
    linear_combination (-(a * (δ : ZMod D))) * hdet'
  obtain ⟨e, he⟩ := hdiv
  have he' : e * (D : ℤ) = A * δ - A' * α := by rw [he]; ring
  have hD : ((D : ℤ) : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne D
  have hγeq : γ = mkSL α β ((N : ℤ) * (D : ℤ) ^ 2 * c₀) δ hdet := by
    rw [eq_mkSL γ]; congr 1 <;> simp [hc₀]
  have key := upperRight_mul_eq α β δ A A' e N D c₀ hdet he' hD
  rw [SL_slash, ← SlashAction.slash_mul]
  have hcast : (((a.val : ℤ) : ℝ) / D) = (A : ℝ) / ((D : ℤ) : ℝ) := by simp [A]
  have hcast' : ((((a * (γ 1 1 : ZMod D) ^ 2).val : ℤ) : ℝ) / D) = (A' : ℝ) / ((D : ℤ) : ℝ) := by
    simp [A', δ]
  rw [hcast, hcast']
  conv_lhs => rw [hγeq]
  rw [show ((mkSL α β ((N : ℤ) * (D : ℤ) ^ 2 * c₀) δ hdet : SL(2, ℤ)) : GL (Fin 2) ℝ) =
    mapGL ℝ (mkSL α β ((N : ℤ) * (D : ℤ) ^ 2 * c₀) δ hdet) from rfl, key,
    SlashAction.slash_mul]
  congr 1
  have hmem := hf _ (gammaPrime_mem α β δ A A' e D c₀ N hdet he')
  rw [SL_slash] at hmem
  exact hmem

lemma unit_of_mem_Gamma0 (N : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 (N * D ^ 2)) :
    IsUnit ((γ 1 1 : ℤ) : ZMod D) := by
  rw [Gamma0_mem] at hγ
  obtain ⟨c₀, hc₀⟩ : ((N * D ^ 2 : ℕ) : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  have h := congrArg (Int.cast : ℤ → ZMod D) (det_SL2 γ)
  rw [hc₀] at h
  push_cast at h
  simp only [ZMod.natCast_self, zero_pow two_ne_zero, mul_zero, zero_mul, sub_zero] at h
  exact IsUnit.of_mul_eq_one_right _ h

/-- **Invariance of the twist.** If `f` is invariant under `Γ₀(N)` and `χ² = 1`, then the twist is
invariant under `Γ₀(N D²)`. -/
theorem twistFun_slash (N : ℕ) (f : ℍ → ℂ) (hf : ∀ γ ∈ Gamma0 N, f ∣[(2 : ℤ)] γ = f)
    (χ : MulChar (ZMod D) ℂ) (hχ : ∀ u : (ZMod D)ˣ, χ u ^ 2 = 1)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 (N * D ^ 2)) :
    twistFun f χ ∣[(2 : ℤ)] γ = twistFun f χ := by
  obtain ⟨u, hu⟩ := unit_of_mem_Gamma0 N γ hγ
  simp only [twistFun, SlashAction.sum_slash, SL_smul_slash, translate_slash N f hf γ hγ]
  have hχu : χ ((u ^ 2 : (ZMod D)ˣ) : ZMod D) = 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow]; exact hχ u
  refine Fintype.sum_equiv (Units.mulRight (u ^ 2)) _ _ (fun a => ?_)
  show _ = χ (a * ↑(u ^ 2)) • _
  rw [map_mul, hχu, mul_one, ← hu]
  rfl

/-! ### Holomorphy and cusp conditions -/

lemma twistFun_mdifferentiable (f : ℍ → ℂ) (hf : MDiff f) (χ : MulChar (ZMod D) ℂ) :
    MDiff (twistFun f χ) := by
  unfold twistFun
  refine MDifferentiable.sum (fun a _ => ?_)
  have h := MDifferentiable.smul (f := fun _ : ℍ => χ a) mdifferentiable_const (hf.slash 2
    (upperRightHom (((a.val : ℤ) : ℝ) / D)))
  exact h

lemma upperRightHom_rat (x : ℚ) :
    (upperRightHom (x : ℚ)).map (Rat.castHom ℝ) = upperRightHom (x : ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Translating a cusp of `SL(2, ℤ)` by a rational number gives a cusp. -/
lemma isCusp_translate {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) (x : ℚ) :
    IsCusp (upperRightHom (x : ℝ) • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨q, rfl⟩ := hc
  refine ⟨upperRightHom x • q, ?_⟩
  classical
  have h := OnePoint.map_smul (Rat.castHom ℝ) (upperRightHom x) q
  rw [upperRightHom_rat] at h
  simpa using h

lemma isZeroAt_zero' (c : OnePoint ℝ) (k : ℤ) : c.IsZeroAt (0 : ℍ → ℂ) k := fun g _ => by
  rw [SlashAction.zero_slash]; exact Filter.zero_zeroAtFilter _

lemma isZeroAt_const_smul {c : OnePoint ℝ} {F : ℍ → ℂ} {k : ℤ} (h : c.IsZeroAt F k) (z : ℂ) :
    c.IsZeroAt (z • F) k := fun g hg => by
  rw [ModularForm.smul_slash]; exact (h g hg).smul _

lemma isZeroAt_sum {c : OnePoint ℝ} {k : ℤ} {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, c.IsZeroAt (F i) k) : c.IsZeroAt (∑ i ∈ s, F i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isZeroAt_zero' c k
  | insert i t hi IH =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (IH fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- The twist vanishes at every cusp. -/
lemma twistFun_isZeroAt (N : ℕ) [NeZero N] (f : CuspForm (Gamma0 N) 2) (χ : MulChar (ZMod D) ℂ)
    {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) : c.IsZeroAt (twistFun f χ) 2 := by
  unfold twistFun
  refine isZeroAt_sum _ _ (fun a _ => isZeroAt_const_smul ?_ _)
  rw [← OnePoint.IsZeroAt.smul_iff]
  apply CuspFormClass.zero_at_cusps f
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
  have h := isCusp_translate hc ((a.val : ℚ) / D)
  have e : (((a.val : ℤ) : ℝ) / D) = (((a.val : ℚ) / D : ℚ) : ℝ) := by push_cast; rfl
  rw [e]; exact h

instance (N : ℕ) [NeZero N] : NeZero (N * D ^ 2) := ⟨by simp [NeZero.ne]⟩

/-- **The twisted cusp form** `Σ_{a mod D} χ(a) f(τ + a/D)`, on `Γ₀(N D²)`. -/
def twistCuspForm (N : ℕ) [NeZero N] (f : CuspForm (Gamma0 N) 2) (χ : MulChar (ZMod D) ℂ)
    (hχ : ∀ u : (ZMod D)ˣ, χ u ^ 2 = 1) : CuspForm (Gamma0 (N * D ^ 2)) 2 where
  toFun := twistFun f χ
  slash_action_eq' γ hγ := by
    obtain ⟨γ0, hγ0, rfl⟩ := Subgroup.mem_map.mp hγ
    have hf : ∀ γ ∈ Gamma0 N, (f : ℍ → ℂ) ∣[(2 : ℤ)] γ = f := fun γ hγ => by
      rw [SL_slash]
      exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)
    have := twistFun_slash N f hf χ hχ γ0 hγ0
    rw [SL_slash] at this
    exact this
  holo' := twistFun_mdifferentiable f (CuspFormClass.holo f) χ
  zero_at_cusps' hc :=
    twistFun_isZeroAt N f χ ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)

lemma coe_twistCuspForm (N : ℕ) [NeZero N] (f : CuspForm (Gamma0 N) 2) (χ : MulChar (ZMod D) ℂ)
    (hχ : ∀ u : (ZMod D)ˣ, χ u ^ 2 = 1) : (twistCuspForm N f χ hχ : ℍ → ℂ) = twistFun f χ := rfl

end PilotA
