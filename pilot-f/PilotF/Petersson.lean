/-
Copyright (c) 2026 Liam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liam
-/
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Petersson inner product on cusp forms

Let `𝒢 ≤ GL(2, ℝ)` be an arithmetic subgroup with determinant one (for instance the image of
`Γ₀(N)`). For cusp forms `f, g` of weight `k` on `𝒢` we define

`⟪f, g⟫ = ∫_{τ ∈ 𝒟} ∑_{h ∈ 𝒮ℒ ⧸ 𝒢} conj (f (h⁻¹ τ)) g (h⁻¹ τ) (im (h⁻¹ τ)) ^ k  dμ(τ)`,

where `𝒟` is the standard fundamental domain of `SL(2, ℤ)` (Mathlib's `ModularGroup.fd`) and
`μ = dx dy / y²` is the invariant measure on `ℍ` (Mathlib's `volume` on `ℍ`). The cosets
`h ∈ 𝒮ℒ ⧸ 𝒢` are taken in `𝒮ℒ`, the image of `SL(2, ℤ)` in `GL(2, ℝ)`. This is the usual
integral over `𝒢 \ ℍ`, unfolded along `SL(2, ℤ)`: no fundamental domain for `𝒢` is needed. It is
not normalized by the index.

## Main results

* `PilotF.volume_fd_lt_top`: `𝒟` has finite invariant measure.
* `PilotF.integrableOn_peterssonSum`: the integrand is integrable on `𝒟` for cusp forms
  (convergence of the Petersson integral).
* `PilotF.peterssonInner`: the inner product.
* `PilotF.peterssonInner_conj_symm`, `peterssonInner_add_left`, `peterssonInner_smul_left`,
  `peterssonInner_self_nonneg`, `peterssonInner_self_eq_zero`: it is a positive definite
  Hermitian form.
* `PilotF.peterssonCore`: the bundled `InnerProductSpace.Core ℂ (CuspForm 𝒢 k)`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Complex Filter Topology Set
open scoped MatrixGroups ComplexConjugate ModularForm Modular Manifold ENNReal NNReal ComplexOrder

noncomputable section

namespace PilotF

/-! ### Measure theory of the fundamental domain -/

lemma measurableSet_fd : MeasurableSet 𝒟 := isClosed_fd.measurableSet

lemma one_half_le_im_of_mem_fd {τ : ℍ} (h : τ ∈ 𝒟) : 1 / 2 ≤ τ.im := by
  have h1 := three_le_four_mul_im_sq_of_mem_fd h
  nlinarith [τ.im_pos]

/-- The weight `1 / y ^ 2` has finite integral over `{y > c}` for `c > 0`. -/
lemma lintegral_Ioi_inv_sq_lt_top {c : ℝ} (hc : 0 < c) :
    ∫⁻ y in Ioi c, ((1 / ‖y‖₊) ^ 2 : ℝ≥0) < ∞ := by
  have hint := integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hc
  have h2 := hint.2
  refine lt_of_eq_of_lt (setLIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_) h2
  have hy : 0 < y := hc.trans hy
  rw [← ofReal_norm, Real.norm_of_nonneg (Real.rpow_nonneg hy.le _)]
  rw [Real.rpow_neg hy.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp [Real.nnnorm_of_nonneg hy.le, one_div, inv_pow]

/-- The standard fundamental domain of `SL(2, ℤ)` has finite invariant measure. -/
theorem volume_fd_lt_top : volume 𝒟 < ∞ := by
  rw [volume_eq_lintegral]
  set T : Set ℂ := {z | |z.re| ≤ 1 / 2 ∧ 1 / 4 < z.im} with hT
  have hsub : ((↑) '' 𝒟 : Set ℂ) ⊆ T := by
    rintro _ ⟨τ, hτ, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [coe_re]; exact hτ.2
    · rw [coe_im]; linarith [one_half_le_im_of_mem_fd hτ]
  refine (lintegral_mono_set hsub).trans_lt ?_
  have hT' : T = measurableEquivRealProd ⁻¹' (Icc (-(1 / 2)) (1 / 2) ×ˢ Ioi (1 / 4)) := by
    ext z
    simp [hT, measurableEquivRealProd_apply, abs_le]
  have key : ∫⁻ z in T, (((1 / ‖z.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) =
      ∫⁻ p in Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ioi (1 / 4 : ℝ), (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) := by
    rw [hT']
    exact volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
      measurableEquivRealProd.measurableEmbedding
      (fun p : ℝ × ℝ ↦ (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) _
  rw [key, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have := lintegral_prod_mul (μ := volume.restrict (Icc (-(1 / 2 : ℝ)) (1 / 2)))
    (ν := volume.restrict (Ioi (1 / 4 : ℝ))) (f := fun _ ↦ 1)
    (g := fun y : ℝ ↦ (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) aemeasurable_const (by fun_prop)
  simp only [one_mul] at this
  rw [this]
  simp only [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Icc]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_Ioi_inv_sq_lt_top (by norm_num))

/-- The invariant measure on `ℍ` charges every nonempty open set. -/
instance : (volume : Measure ℍ).IsOpenPosMeasure := by
  refine ⟨fun U hU hne h ↦ ?_⟩
  rw [volume_eq_lintegral] at h
  have hV : IsOpen (((↑) : ℍ → ℂ) '' U) := isOpenEmbedding_coe.isOpenMap U hU
  rw [lintegral_eq_zero_iff (by fun_prop), Filter.EventuallyEq,
    ae_restrict_iff' hV.measurableSet] at h
  have h0 : volume (((↑) : ℍ → ℂ) '' U) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with z hz hzV
    have := hz hzV
    obtain ⟨τ, -, rfl⟩ := hzV
    simp [τ.im_pos.ne'] at this
  exact hV.measure_ne_zero volume (hne.image _) h0

lemma nonempty_fdo : (𝒟ᵒ).Nonempty :=
  closure_nonempty_iff.mp ⟨I, fd_eq_closure_fdo ▸ I_mem_fd⟩

/-- **Identity theorem** on `ℍ`: a holomorphic function vanishing on `𝒟ᵒ` vanishes. -/
lemma eq_zero_of_eqOn_fdo {f : ℍ → ℂ} (hf : MDiff f) (h0 : EqOn f 0 𝒟ᵒ) : f = 0 := by
  have han : AnalyticOnNhd ℂ (f ∘ ofComplex) {z | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd isOpen_upperHalfPlaneSet
  obtain ⟨τ₀, hτ₀⟩ := nonempty_fdo
  have hev : f ∘ ofComplex =ᶠ[𝓝 (τ₀ : ℂ)] 0 := by
    refine eventually_of_mem ((isOpenEmbedding_coe.isOpenMap _ isOpen_fdo).mem_nhds
      ⟨τ₀, hτ₀, rfl⟩) ?_
    rintro _ ⟨τ, hτ, rfl⟩
    simp [ofComplex_apply, h0 hτ]
  have hpre : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre τ₀.im_pos hev
  funext τ
  simpa [ofComplex_apply] using this τ.im_pos

/-! ### The Petersson integrand -/

lemma petersson_self_eq (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    petersson k f f τ = ((‖f τ‖ ^ 2 * τ.im ^ k : ℝ) : ℂ) := by
  simp [petersson, Complex.conj_mul', ofReal_zpow]

lemma petersson_add_left (k : ℤ) (f₁ f₂ f' : ℍ → ℂ) (τ : ℍ) :
    petersson k (f₁ + f₂) f' τ = petersson k f₁ f' τ + petersson k f₂ f' τ := by
  simp [petersson, add_mul]

lemma petersson_smul_left (k : ℤ) (c : ℂ) (f f' : ℍ → ℂ) (τ : ℍ) :
    petersson k (c • f) f' τ = conj c * petersson k f f' τ := by
  simp [petersson, mul_assoc]

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] [𝒢.HasDetOne] {k : ℤ}

local notation "𝒬" => 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)

/-- The term of the Petersson integrand indexed by a coset `h 𝒢 ∈ 𝒮ℒ ⧸ 𝒢`:
`τ ↦ petersson k f f' (h⁻¹ τ)`. -/
def peterssonTerm (f f' : CuspForm 𝒢 k) (q : 𝒬) (τ : ℍ) : ℂ :=
  petersson k f f' ((q.out : GL (Fin 2) ℝ)⁻¹ • τ)

@[simp] lemma peterssonTerm_mk (f f' : CuspForm 𝒢 k) (h : 𝒮ℒ) (τ : ℍ) :
    peterssonTerm f f' ⟦h⟧ τ = petersson k f f' ((h : GL (Fin 2) ℝ)⁻¹ • τ) := by
  obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (𝒢.subgroupOf 𝒮ℒ) h
  have hj' : ((QuotientGroup.mk h : 𝒬).out : GL (Fin 2) ℝ) = h * ((j : 𝒮ℒ) : GL (Fin 2) ℝ) := by
    rw [← Subgroup.coe_mul, ← hj]
  show petersson k f f' (((QuotientGroup.mk h : 𝒬).out : GL (Fin 2) ℝ)⁻¹ • τ) = _
  rw [hj', mul_inv_rev, mul_smul]
  exact SlashInvariantFormClass.petersson_smul (inv_mem j.2)

/-- The Petersson integrand `τ ↦ ∑_{h ∈ 𝒮ℒ ⧸ 𝒢} petersson k f f' (h⁻¹ τ)`, a function on `ℍ`
invariant under `SL(2, ℤ)`. -/
def peterssonSum (f f' : CuspForm 𝒢 k) (τ : ℍ) : ℂ :=
  Finset.sum (@Finset.univ 𝒬 (Fintype.ofFinite 𝒬)) fun q ↦ peterssonTerm f f' q τ

lemma peterssonSum_eq [Fintype 𝒬] (f f' : CuspForm 𝒢 k) (τ : ℍ) :
    peterssonSum f f' τ = ∑ q : 𝒬, peterssonTerm f f' q τ := by
  simp only [peterssonSum]
  congr
  exact Subsingleton.elim _ _

lemma continuous_peterssonTerm (f f' : CuspForm 𝒢 k) (q : 𝒬) :
    Continuous (peterssonTerm f f' q) := by
  exact (petersson_continuous k (ModularFormClass.holo f).continuous
    (ModularFormClass.holo f').continuous).comp (continuous_const_smul _)

lemma continuous_peterssonSum (f f' : CuspForm 𝒢 k) : Continuous (peterssonSum f f') := by
  let : Fintype 𝒬 := Fintype.ofFinite _
  simp_rw [funext (peterssonSum_eq f f')]
  exact continuous_finsetSum _ fun q _ ↦ continuous_peterssonTerm f f' q

/-- The Petersson integrand of two cusp forms is bounded on `ℍ`. -/
lemma exists_bound_peterssonSum (f f' : CuspForm 𝒢 k) :
    ∃ C, ∀ τ, ‖peterssonSum f f' τ‖ ≤ C := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k 𝒢 f f'
  let : Fintype 𝒬 := Fintype.ofFinite _
  refine ⟨Fintype.card 𝒬 * C, fun τ ↦ ?_⟩
  rw [peterssonSum_eq]
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  induction q using Quotient.inductionOn with
  | h h => exact hC _

/-- **Convergence of the Petersson integral**: for cusp forms the integrand is integrable on
the fundamental domain `𝒟`. -/
theorem integrableOn_peterssonSum (f f' : CuspForm 𝒢 k) :
    IntegrableOn (peterssonSum f f') 𝒟 := by
  obtain ⟨C, hC⟩ := exists_bound_peterssonSum f f'
  exact Measure.integrableOn_of_bounded volume_fd_lt_top.ne
    (continuous_peterssonSum f f').aestronglyMeasurable (ae_of_all _ hC)

lemma peterssonSum_add_left (f₁ f₂ f' : CuspForm 𝒢 k) (τ : ℍ) :
    peterssonSum (f₁ + f₂) f' τ = peterssonSum f₁ f' τ + peterssonSum f₂ f' τ := by
  let : Fintype 𝒬 := Fintype.ofFinite _
  simp only [peterssonSum_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  induction q using Quotient.inductionOn with
  | h h => simp [FunLike.coe_add, petersson_add_left]

lemma peterssonSum_smul_left (c : ℂ) (f f' : CuspForm 𝒢 k) (τ : ℍ) :
    peterssonSum (c • f) f' τ = conj c * peterssonSum f f' τ := by
  let : Fintype 𝒬 := Fintype.ofFinite _
  simp only [peterssonSum_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  induction q using Quotient.inductionOn with
  | h h => simp [petersson_smul_left]

lemma peterssonSum_symm (f f' : CuspForm 𝒢 k) (τ : ℍ) :
    peterssonSum f' f τ = conj (peterssonSum f f' τ) := by
  let : Fintype 𝒬 := Fintype.ofFinite _
  simp only [peterssonSum_eq, map_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  induction q using Quotient.inductionOn with
  | h h => exact petersson_symm k f f' _

lemma peterssonTerm_self_re_nonneg (f : CuspForm 𝒢 k) (q : 𝒬) (τ : ℍ) :
    0 ≤ (peterssonTerm f f q τ).re := by
  induction q using Quotient.inductionOn with
  | h h =>
    rw [peterssonTerm_mk, petersson_self_eq, ofReal_re]
    exact mul_nonneg (sq_nonneg _) (zpow_nonneg (im_pos _).le _)

lemma peterssonSum_self_eq_re (f : CuspForm 𝒢 k) (τ : ℍ) :
    peterssonSum f f τ = ((peterssonSum f f τ).re : ℂ) := by
  let : Fintype 𝒬 := Fintype.ofFinite _
  rw [peterssonSum_eq, re_sum, ofReal_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  induction q using Quotient.inductionOn with
  | h h => rw [peterssonTerm_mk, petersson_self_eq, ofReal_re]

lemma peterssonSum_self_re_nonneg (f : CuspForm 𝒢 k) (τ : ℍ) :
    0 ≤ (peterssonSum f f τ).re := by
  let : Fintype 𝒬 := Fintype.ofFinite _
  rw [peterssonSum_eq, re_sum]
  exact Finset.sum_nonneg fun q _ ↦ peterssonTerm_self_re_nonneg f q τ

/-- The identity coset contributes `‖f τ‖ ^ 2 (im τ) ^ k`, so this bounds the integrand. -/
lemma norm_sq_mul_le_peterssonSum (f : CuspForm 𝒢 k) (τ : ℍ) :
    ‖f τ‖ ^ 2 * τ.im ^ k ≤ (peterssonSum f f τ).re := by
  let : Fintype 𝒬 := Fintype.ofFinite _
  rw [peterssonSum_eq, re_sum]
  have hterm : (peterssonTerm f f ⟦1⟧ τ).re = ‖f τ‖ ^ 2 * τ.im ^ k := by
    rw [peterssonTerm_mk, petersson_self_eq, ofReal_re]
    simp
  rw [← hterm]
  exact Finset.single_le_sum (f := fun q ↦ (peterssonTerm f f q τ).re)
    (fun q _ ↦ peterssonTerm_self_re_nonneg f q τ) (Finset.mem_univ ⟦1⟧)

/-! ### The inner product -/

/-- The **Petersson inner product** `⟪f, f'⟫ = ∫_𝒟 ∑_{h ∈ 𝒮ℒ ⧸ 𝒢} conj (f (h⁻¹ τ)) f' (h⁻¹ τ)
(im (h⁻¹ τ)) ^ k dμ(τ)` of two cusp forms on `𝒢`. It is conjugate linear in `f`. -/
def peterssonInner (f f' : CuspForm 𝒢 k) : ℂ :=
  ∫ τ in 𝒟, peterssonSum f f' τ

lemma peterssonInner_conj_symm (f f' : CuspForm 𝒢 k) :
    conj (peterssonInner f' f) = peterssonInner f f' := by
  simp only [peterssonInner, ← integral_conj, peterssonSum_symm f f', conj_conj]

lemma peterssonInner_add_left (f₁ f₂ f' : CuspForm 𝒢 k) :
    peterssonInner (f₁ + f₂) f' = peterssonInner f₁ f' + peterssonInner f₂ f' := by
  simp only [peterssonInner, peterssonSum_add_left]
  exact integral_add (integrableOn_peterssonSum f₁ f') (integrableOn_peterssonSum f₂ f')

lemma peterssonInner_smul_left (c : ℂ) (f f' : CuspForm 𝒢 k) :
    peterssonInner (c • f) f' = conj c * peterssonInner f f' := by
  simp only [peterssonInner, peterssonSum_smul_left, integral_const_mul]

lemma peterssonInner_add_right (f f₁' f₂' : CuspForm 𝒢 k) :
    peterssonInner f (f₁' + f₂') = peterssonInner f f₁' + peterssonInner f f₂' := by
  rw [← peterssonInner_conj_symm, peterssonInner_add_left, map_add, peterssonInner_conj_symm,
    peterssonInner_conj_symm]

lemma peterssonInner_smul_right (c : ℂ) (f f' : CuspForm 𝒢 k) :
    peterssonInner f (c • f') = c * peterssonInner f f' := by
  rw [← peterssonInner_conj_symm, peterssonInner_smul_left, map_mul, conj_conj,
    peterssonInner_conj_symm]

/-- `⟪f, f⟫` is the real number `∫_𝒟 ∑_h ‖f (h⁻¹ τ)‖ ^ 2 (im (h⁻¹ τ)) ^ k dμ`. -/
lemma peterssonInner_self_eq (f : CuspForm 𝒢 k) :
    peterssonInner f f = ((∫ τ in 𝒟, (peterssonSum f f τ).re : ℝ) : ℂ) := by
  rw [peterssonInner, ← integral_complex_ofReal]
  exact integral_congr_ae (ae_of_all _ fun τ ↦ peterssonSum_self_eq_re f τ)

/-- **Positivity**: `0 ≤ ⟪f, f⟫` (in particular `⟪f, f⟫` is real). -/
theorem peterssonInner_self_nonneg (f : CuspForm 𝒢 k) : 0 ≤ peterssonInner f f := by
  rw [peterssonInner_self_eq]
  exact_mod_cast setIntegral_nonneg measurableSet_fd fun τ _ ↦ peterssonSum_self_re_nonneg f τ

lemma re_peterssonInner_self_nonneg (f : CuspForm 𝒢 k) : 0 ≤ (peterssonInner f f).re := by
  rw [peterssonInner_self_eq, ofReal_re]
  exact setIntegral_nonneg measurableSet_fd fun τ _ ↦ peterssonSum_self_re_nonneg f τ

/-- **Definiteness**: `⟪f, f⟫ = 0` only for `f = 0`. -/
theorem peterssonInner_self_eq_zero {f : CuspForm 𝒢 k} : peterssonInner f f = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  swap
  · subst h
    have h0 : ∀ τ, peterssonSum (0 : CuspForm 𝒢 k) 0 τ = 0 := fun τ ↦ by
      simpa using peterssonSum_smul_left (0 : ℂ) (0 : CuspForm 𝒢 k) 0 τ
    simp [peterssonInner, h0]
  rw [peterssonInner_self_eq, ofReal_eq_zero] at h
  have hint : IntegrableOn (fun τ ↦ (peterssonSum f f τ).re) 𝒟 :=
    (integrableOn_peterssonSum f f).re
  rw [setIntegral_eq_zero_iff_of_nonneg_ae
    (ae_of_all _ fun τ ↦ peterssonSum_self_re_nonneg f τ) hint] at h
  have h' := ae_restrict_of_ae_restrict_of_subset fdo_subset_fd h
  have hzero := Measure.eqOn_open_of_ae_eq h' isOpen_fdo
    (continuous_re.comp (continuous_peterssonSum f f)).continuousOn continuousOn_const
  have hf0 : EqOn (f : ℍ → ℂ) 0 𝒟ᵒ := fun τ hτ ↦ by
    have h1 := norm_sq_mul_le_peterssonSum f τ
    have h0 := hzero hτ
    simp only [Pi.zero_apply] at h0
    rw [h0] at h1
    have h2 : 0 < τ.im ^ k := zpow_pos τ.im_pos k
    have h3 : ‖f τ‖ ^ 2 ≤ 0 := by
      by_contra hc
      exact absurd h1 (not_le.mpr (mul_pos (lt_of_not_ge hc) h2))
    have h4 : ‖f τ‖ = 0 := pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h3 (sq_nonneg _))
    simpa using h4
  ext τ
  simpa using congrFun (eq_zero_of_eqOn_fdo (ModularFormClass.holo f) hf0) τ

/-- The Petersson inner product makes `S_k(𝒢)` an inner product space. -/
@[instance_reducible]
def peterssonCore : InnerProductSpace.Core ℂ (CuspForm 𝒢 k) where
  inner f f' := peterssonInner f f'
  conj_inner_symm f f' := peterssonInner_conj_symm f f'
  re_inner_nonneg f := re_peterssonInner_self_nonneg f
  add_left := peterssonInner_add_left
  smul_left f f' c := peterssonInner_smul_left c f f'
  definite _ h := peterssonInner_self_eq_zero.mp h

end PilotF
