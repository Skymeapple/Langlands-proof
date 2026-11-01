/-
Copyright (c) 2026 Liam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liam
-/
import PilotF.Unfolding
import PilotD.Newforms

/-!
# Newforms as the Petersson complement of oldforms

Pilot D defines the new subspace of `S_k(Γ₀(N))` as the common kernel of the traces
`Tr_{N/p}` and `Tr_{N/p} ∘ W_N` (`CuspForm.newSubspace`). The classical definition is the
Petersson orthogonal complement of the old subspace. We state the equivalence for every `N`
(`NewSubspaceEqOrthogonal`) and prove it for `N` prime.

## Main results

* `PilotF.peterssonInner_eq_peterssonInner_trace`: `⟪g, f⟫_{Γ₀(N)} = ⟪g, Tr f⟫_{SL(2, ℤ)}` for `g`
  of level one (the trace is the adjoint of the inclusion).
* `PilotF.peterssonInner_fricke`, `peterssonInner_fricke_left`: `W_N` is unitary and self-adjoint.
* `PilotF.NewSubspaceEqOrthogonal`: the statement, for all `N`.
* `PilotF.newSubspaceEqOrthogonal_prime`: it holds for `N = p` prime.
-/

open UpperHalfPlane ModularGroup MeasureTheory Complex Set CongruenceSubgroup
open scoped MatrixGroups ComplexConjugate ModularForm Modular Manifold

noncomputable section

namespace PilotF

variable {k : ℤ}

section General

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] [𝒢.HasDetOne]

/-- The Petersson orthogonal complement of a subspace of `S_k(𝒢)`. -/
def peterssonOrthogonal (K : Submodule ℂ (CuspForm 𝒢 k)) : Submodule ℂ (CuspForm 𝒢 k) where
  carrier := {f | ∀ g ∈ K, peterssonInner g f = 0}
  add_mem' {a b} ha hb g hg := by rw [peterssonInner_add_right, ha g hg, hb g hg, add_zero]
  zero_mem' g _ := by simpa using peterssonInner_smul_right 0 g 0
  smul_mem' c a ha g hg := by rw [peterssonInner_smul_right, ha g hg, mul_zero]

lemma mem_peterssonOrthogonal {K : Submodule ℂ (CuspForm 𝒢 k)} {f : CuspForm 𝒢 k} :
    f ∈ peterssonOrthogonal K ↔ ∀ g ∈ K, peterssonInner g f = 0 :=
  Iff.rfl

/-- The forms `g` with `⟪g, f⟫ = 0`, a submodule. -/
def leftOrth (f : CuspForm 𝒢 k) : Submodule ℂ (CuspForm 𝒢 k) where
  carrier := {g | peterssonInner g f = 0}
  add_mem' {a b} ha hb := by
    simp only [mem_ofPred_eq] at *; rw [peterssonInner_add_left, ha, hb, add_zero]
  zero_mem' := by simpa using peterssonInner_smul_left 0 (0 : CuspForm 𝒢 k) f
  smul_mem' c a ha := by
    simp only [mem_ofPred_eq] at *; rw [peterssonInner_smul_left, ha, mul_zero]

lemma mem_peterssonOrthogonal_iSup {ι : Sort*} {K : ι → Submodule ℂ (CuspForm 𝒢 k)}
    {f : CuspForm 𝒢 k} :
    f ∈ peterssonOrthogonal (⨆ i, K i) ↔ ∀ i, ∀ g ∈ K i, peterssonInner g f = 0 := by
  refine ⟨fun h i g hg ↦ h g (le_iSup K i hg), fun h g hg ↦ ?_⟩
  have : (⨆ i, K i) ≤ leftOrth f := iSup_le fun i g hg ↦ h i g hg
  exact this hg

/-- If `𝒮ℒ ≤ 𝒢` the coset sum has one term. -/
lemma peterssonSum_of_le (h : 𝒮ℒ ≤ 𝒢) (f f' : CuspForm 𝒢 k) (τ : ℍ) :
    peterssonSum f f' τ = petersson k f f' τ := by
  let : Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) := Fintype.ofFinite _
  rw [peterssonSum_eq, Finset.sum_eq_single (QuotientGroup.mk 1)]
  · simp
  · intro q _ hq
    exfalso
    induction q using Quotient.inductionOn with
    | h a =>
      refine hq (QuotientGroup.eq.mpr ?_)
      rw [Subgroup.mem_subgroupOf]
      simpa using h a.2
  · simp

lemma peterssonInner_of_le (h : 𝒮ℒ ≤ 𝒢) (f f' : CuspForm 𝒢 k) :
    peterssonInner f f' = ∫ τ in 𝒟, petersson k f f' τ := by
  simp only [peterssonInner, peterssonSum_of_le h]

/-- **The trace is adjoint to the inclusion**: for `g` of level one (`ℋ = 𝒮ℒ`), the Petersson
integrand of `g` and `f` on `𝒢` is the level one integrand of `g` and `Tr f`. -/
lemma peterssonSum_eq_petersson_trace {ℋ : Subgroup (GL (Fin 2) ℝ)} (hℋ : ℋ = 𝒮ℒ)
    [𝒢.IsFiniteRelIndex ℋ] (G : CuspForm ℋ k) (g f : CuspForm 𝒢 k) (hg : ⇑g = ⇑G) (τ : ℍ) :
    peterssonSum g f τ = petersson k G (CuspForm.trace ℋ f) τ := by
  subst hℋ
  let : Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) := Fintype.ofFinite _
  rw [peterssonSum_eq, CuspForm.coe_trace]
  simp only [petersson, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  induction q using Quotient.inductionOn with
  | h a =>
    rw [peterssonTerm_mk, SlashInvariantForm.quotientFunc_mk]
    have hdet : (a : GL (Fin 2) ℝ)⁻¹.det = 1 := Subgroup.HasDetOne.det_eq (inv_mem a.2)
    have hdet' : ((a : GL (Fin 2) ℝ)⁻¹.det : ℝ) = 1 := by rw [hdet]; rfl
    have h := petersson_slash k G f (a : GL (Fin 2) ℝ)⁻¹ τ
    have hdetA : ((a : GL (Fin 2) ℝ).det : ℝ) = 1 := by
      rw [Subgroup.HasDetOne.det_eq a.2]; rfl
    have hσ : σ (a : GL (Fin 2) ℝ)⁻¹ = ContinuousAlgEquiv.refl ℝ ℂ := by simp [σ, hdetA]
    rw [hdet', abs_one, Complex.ofReal_one, one_zpow, one_mul, hσ,
      ContinuousAlgEquiv.refl_apply,
      SlashInvariantFormClass.slash_action_eq G _ (inv_mem a.2)] at h
    rw [← hg] at h ⊢
    exact h.symm

/-- `⟪g, f⟫_𝒢 = ⟪g, Tr f⟫_{SL(2, ℤ)}` for `g` of level one. -/
theorem peterssonInner_eq_peterssonInner_trace {ℋ : Subgroup (GL (Fin 2) ℝ)} [ℋ.IsArithmetic]
    [ℋ.HasDetOne] (hℋ : ℋ = 𝒮ℒ) [𝒢.IsFiniteRelIndex ℋ] (G : CuspForm ℋ k)
    (g f : CuspForm 𝒢 k) (hg : ⇑g = ⇑G) :
    peterssonInner g f = peterssonInner G (CuspForm.trace ℋ f) := by
  rw [peterssonInner_of_le (𝒢 := ℋ) (by rw [hℋ]) G, peterssonInner]
  simp only [peterssonSum_eq_petersson_trace hℋ G g f hg]

lemma forall_peterssonInner_eq_zero_iff (F : CuspForm 𝒢 k) :
    (∀ G : CuspForm 𝒢 k, peterssonInner G F = 0) ↔ F = 0 := by
  refine ⟨fun h ↦ peterssonInner_self_eq_zero.mp (h F), fun h G ↦ ?_⟩
  subst h
  simpa using peterssonInner_smul_right 0 G 0

end General

/-! ### `Γ₀(N)` and the Fricke involution -/

lemma Gamma0_one_eq_top : Gamma0 1 = ⊤ := by
  ext γ
  simp [Gamma0_mem, Subsingleton.elim ((γ 1 0 : ℤ) : ZMod 1) 0]

lemma Gamma0_one_GL : (Gamma0 1 : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  rw [MonoidHom.range_eq_map, ← Gamma0_one_eq_top]

lemma Gamma0_le_SL (N : ℕ) : (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
  Subgroup.map_le_range _ _

variable (N : ℕ) [NeZero N]

lemma frickeMatrix_conj_mem {γ : GL (Fin 2) ℝ} (hγ : γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    frickeMatrix N * γ * (frickeMatrix N)⁻¹ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := by
  have := Gamma0_le_conj_frickeMatrix N hγ
  rwa [map_inv, Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul] at this

lemma frickeMatrix_inv_conj_mem {γ : GL (Fin 2) ℝ}
    (hγ : γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    (frickeMatrix N)⁻¹ * γ * frickeMatrix N ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := by
  rw [← conj_frickeMatrix_Gamma0 N, map_inv, Subgroup.mem_inv_pointwise_smul_iff,
    ConjAct.toConjAct_smul]
  simpa [mul_assoc] using hγ

/-- **`W_N` is unitary** for the Petersson inner product. -/
theorem peterssonInner_fricke (f g : CuspForm (Gamma0 N) k) :
    peterssonInner (CuspForm.fricke N f) (CuspForm.fricke N g) = peterssonInner f g :=
  peterssonInner_map_eq (CuspForm.fricke N) (fun f ↦ peterssonInner_self_slash (Gamma0_le_SL N)
    (frickeMatrix N) (Units.ext (det_frickeMatrix N)) (fun _ hγ ↦ frickeMatrix_inv_conj_mem N hγ)
    (fun _ hγ ↦ frickeMatrix_conj_mem N hγ) f _ (CuspForm.coe_fricke N f)) f g

/-- **`W_N` is self-adjoint** for the Petersson inner product. -/
theorem peterssonInner_fricke_left (f g : CuspForm (Gamma0 N) k) :
    peterssonInner (CuspForm.fricke N f) g = peterssonInner f (CuspForm.fricke N g) := by
  conv_lhs => rw [← CuspForm.fricke_fricke N g]
  exact peterssonInner_fricke N f _

/-! ### The statement and the prime level case -/

/-- **Newforms are the Petersson complement of oldforms** (statement): Pilot D's trace-kernel
new subspace of `S_k(Γ₀(N))` equals the Petersson orthogonal complement of the old subspace. -/
def NewSubspaceEqOrthogonal (N : ℕ) [NeZero N] (k : ℤ) : Prop :=
  CuspForm.newSubspace N k = peterssonOrthogonal (CuspForm.oldSubspace N k)

variable {N}

omit [NeZero N] in
lemma levelRaise_one_apply (h : 1 * 1 ∣ N) (g : CuspForm (Gamma0 1) k) :
    ⇑(CuspForm.levelRaise 1 1 N h g) = ⇑g := by
  funext τ
  rw [CuspForm.levelRaise_apply]
  congr 1
  ext
  simp [CuspForm.coe_levelRaiseMatrix_smul]

/-- `⟪B_1 g, f⟫_{Γ₀(N)} = ⟪g, Tr f⟫_{Γ₀(1)}`. -/
lemma peterssonInner_levelRaise_one (h : 1 * 1 ∣ N) (g : CuspForm (Gamma0 1) k)
    (f : CuspForm (Gamma0 N) k) :
    peterssonInner (CuspForm.levelRaise 1 1 N h g) f =
      peterssonInner g (CuspForm.traceₗ 1 N f) :=
  peterssonInner_eq_peterssonInner_trace Gamma0_one_GL g _ f (levelRaise_one_apply h g)

/-- A level one form satisfies `g (-1 / z) = z ^ k g z`. -/
lemma level_one_S (g : CuspForm (Gamma0 1) k) (z : ℍ) :
    g (ModularGroup.S • z) = (z : ℂ) ^ k * g z := by
  have hS : (ModularGroup.S : GL (Fin 2) ℝ) ∈ (Gamma0 1 : Subgroup (GL (Fin 2) ℝ)) := by
    rw [Gamma0_one_GL]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have h := congrFun (SlashInvariantFormClass.slash_action_eq g _ hS) z
  have h2 := SlashInvariantForm.slash_S_apply (⇑g) k z
  rw [ModularForm.SL_slash] at h2
  rw [h2, ← modular_S_smul] at h
  rw [← h, mul_comm, mul_assoc, ← zpow_add₀ z.ne_zero, neg_add_cancel, zpow_zero, mul_one]

/-- `B_p g = (√p) ^ (-k) • W_p (B_1 g)` for `g` of level one. -/
lemma levelRaise_eq_smul_fricke (p : ℕ) [NeZero p] (h1 : 1 * 1 ∣ p) (hp : 1 * p ∣ p)
    (g : CuspForm (Gamma0 1) k) :
    CuspForm.levelRaise 1 p p hp g =
      ((√(p : ℝ) : ℂ) ^ (-k)) • CuspForm.fricke p (CuspForm.levelRaise 1 1 p h1 g) := by
  ext τ
  have hs : (√(p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p))
  have hN : (√(p : ℝ) : ℂ) * √(p : ℝ) = p := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg p)
  have hpt : frickeMatrix p • τ = ModularGroup.S • (levelRaiseMatrix p • τ) := by
    ext
    rw [ModularForm.coe_frickeMatrix_smul, modular_S_smul]
    simp [CuspForm.coe_levelRaiseMatrix_smul, div_eq_mul_inv]
  have hfr : CuspForm.fricke p (CuspForm.levelRaise 1 1 p h1 g) τ =
      (√(p : ℝ) * (τ : ℂ)) ^ (-k) * g (frickeMatrix p • τ) := by
    have hsR : √(p : ℝ) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p))
    rw [CuspForm.coe_fricke, ModularForm.slash_apply, levelRaise_one_apply h1 g]
    simp [σ, denom, coe_frickeMatrix, hsR]
    ring
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have key : (√(p : ℝ) : ℂ) ^ (-k) * ((√(p : ℝ) * (τ : ℂ)) ^ (-k) * ((p : ℂ) * τ) ^ k) = 1 := by
    have ha : (√(p : ℝ) : ℂ) ^ k ≠ 0 := zpow_ne_zero _ hs
    have hb : ((√(p : ℝ) : ℂ) * τ) ^ k ≠ 0 := zpow_ne_zero _ (mul_ne_zero hs hτ)
    rw [← hN, mul_assoc, mul_zpow (√(p : ℝ) : ℂ) (√(p : ℝ) * (τ : ℂ)), zpow_neg, zpow_neg]
    field_simp
  rw [smul_apply, hfr, hpt, level_one_S, CuspForm.levelRaise_apply,
    CuspForm.coe_levelRaiseMatrix_smul, smul_eq_mul]
  calc g (levelRaiseMatrix p • τ) = 1 * g (levelRaiseMatrix p • τ) := (one_mul _).symm
    _ = _ := by rw [← key]; ring

lemma traceₗ_eq_zero_iff_of_eq {M p : ℕ} [NeZero p] (hM : M = 1) (f : CuspForm (Gamma0 p) k) :
    CuspForm.traceₗ M p f = 0 ↔ CuspForm.traceₗ 1 p f = 0 := by
  subst hM; rfl

/-- **Newforms of prime level are the Petersson complement of the oldforms.** -/
theorem newSubspaceEqOrthogonal_prime {p : ℕ} (hp : p.Prime) [NeZero p] :
    NewSubspaceEqOrthogonal p k := by
  have h1 : 1 * 1 ∣ p := by simp
  have hpp : 1 * p ∣ p := by simp
  have hTr : ∀ f : CuspForm (Gamma0 p) k,
      (∀ g : CuspForm (Gamma0 1) k,
        peterssonInner (CuspForm.levelRaise 1 1 p h1 g) f = 0) ↔ CuspForm.traceₗ 1 p f = 0 := by
    intro f
    simp only [peterssonInner_levelRaise_one]
    exact forall_peterssonInner_eq_zero_iff _
  have hTrW : ∀ f : CuspForm (Gamma0 p) k,
      (∀ g : CuspForm (Gamma0 1) k,
        peterssonInner (CuspForm.levelRaise 1 p p hpp g) f = 0) ↔
        CuspForm.traceₗ 1 p (CuspForm.fricke p f) = 0 := by
    intro f
    rw [← hTr]
    have hs : (√(p : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < p := by exact_mod_cast hp.pos
      exact_mod_cast (Real.sqrt_pos.mpr this).ne'
    have hc : conj ((√(p : ℝ) : ℂ) ^ (-k)) ≠ 0 := by
      rw [map_ne_zero]
      exact zpow_ne_zero _ hs
    refine forall_congr' fun g ↦ ?_
    rw [levelRaise_eq_smul_fricke p h1 hpp, peterssonInner_smul_left,
      peterssonInner_fricke_left, mul_eq_zero, or_iff_right hc]
  unfold NewSubspaceEqOrthogonal
  ext f
  rw [CuspForm.newSubspace, CuspForm.oldSubspace,
    mem_peterssonOrthogonal_iSup, hp.primeFactors]
  simp only [Finset.mem_singleton, Submodule.mem_iInf, Submodule.mem_inf, LinearMap.mem_ker,
    LinearMap.coe_comp, Function.comp_apply, forall_eq]
  rw [traceₗ_eq_zero_iff_of_eq (Nat.div_self hp.pos), traceₗ_eq_zero_iff_of_eq (Nat.div_self hp.pos)]
  rw [← hTr, ← hTrW]
  constructor
  · rintro ⟨hA, hB⟩ ⟨⟨M, d⟩, hdvd, hlt⟩ g ⟨g₀, rfl⟩
    simp only at hdvd hlt
    have hM : M = 1 := by
      rcases hp.eq_one_or_self_of_dvd M (dvd_of_mul_right_dvd hdvd) with h | h
      · exact h
      · omega
    subst hM
    rcases hp.eq_one_or_self_of_dvd d (by simpa using hdvd) with h | h
    · subst h; exact hA g₀
    · subst h; exact hB g₀
  · intro h
    exact ⟨fun g ↦ h ⟨(1, 1), h1, hp.one_lt⟩ _ ⟨g, rfl⟩,
      fun g ↦ h ⟨(1, p), hpp, hp.one_lt⟩ _ ⟨g, rfl⟩⟩

/-- The Petersson inner product on `S_k(Γ₀(N))`, bundled. -/
example (N : ℕ) [NeZero N] : InnerProductSpace.Core ℂ (CuspForm (Gamma0 N) k) := peterssonCore

/-- For `p` prime, `S_k^new(Γ₀(p))` (traces) is the Petersson complement of `S_k^old(Γ₀(p))`. -/
theorem newSubspace_eq_peterssonOrthogonal_oldSubspace {p : ℕ} (hp : p.Prime) [NeZero p] :
    CuspForm.newSubspace p k = peterssonOrthogonal (CuspForm.oldSubspace p k) :=
  newSubspaceEqOrthogonal_prime hp

end PilotF
