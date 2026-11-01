/-
Copyright (c) 2026 Liam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liam
-/
import PilotF.Petersson
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Invariance of the Petersson inner product under normalizing matrices

Let `𝒢 ≤ 𝒮ℒ` be arithmetic and let `W ∈ GL(2, ℝ)` have determinant one and normalize `𝒢`
(for instance the Fricke matrix `W_N` and `𝒢 = Γ₀(N)`). We prove `⟪f ∣ W, f' ∣ W⟫ = ⟪f, f'⟫`.

The inner product is defined by integrating over the fundamental domain `𝒟` of `SL(2, ℤ)` and
summing over coset representatives, so `W` does not act on the domain of integration. The proof
is the classical unfolding argument, done with Lebesgue integrals of nonnegative functions:

1. `∫_𝒟 ∑_q v (h_q⁻¹ τ) = ∫_ℍ v · R` with `R τ = ∑_q 𝟙_𝒟 (h_q τ)` (`lintegral_fd_sum_eq`).
2. The translates of `𝒟` cover `ℍ` exactly twice outside a null set
   (`tsum_indicator_fd_smul`; the boundary `𝒟 \ 𝒟ᵒ` is null, `volume_fd_diff_fdo`), so
   `∑_{γ ∈ 𝒢} R (γ τ) = 2` almost everywhere, and the same holds for `R ∘ W⁻¹`.
3. Any two such weights give the same integral against a `𝒢`-invariant function
   (`lintegral_mul_eq_of_tsum_eq_two`), and `μ` is `GL(2, ℝ)`-invariant.
4. Polarization extends `⟪f ∣ W, f ∣ W⟫ = ⟪f, f⟫` to the sesquilinear statement.
-/

open UpperHalfPlane ModularGroup MeasureTheory Complex Filter Topology Set
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ComplexConjugate ModularForm Modular Manifold ENNReal NNReal

noncomputable section

namespace PilotF

/-! ### The boundary of `𝒟` is null -/

lemma volume_eq_zero_of_coe {s : Set ℍ} (hs : volume (((↑) : ℍ → ℂ) '' s) = 0) :
    volume s = 0 := by
  rw [volume_def]
  refine withDensity_absolutelyContinuous _ _ ?_
  rwa [measurableEmbedding_coe.comap_apply]

lemma volume_re_eq (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have : {z : ℂ | z.re = c} = measurableEquivRealProd ⁻¹' ({c} ×ˢ univ) := by
    ext z; simp [measurableEquivRealProd_apply]
  rw [this, volume_preserving_equiv_real_prod.measure_preimage_equiv, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_singleton, zero_mul]

lemma volume_fd_diff_fdo : volume (𝒟 \ 𝒟ᵒ) = 0 := by
  apply volume_eq_zero_of_coe
  have hsub : ((↑) '' (𝒟 \ 𝒟ᵒ) : Set ℂ) ⊆
      ({z | z.re = 1 / 2} ∪ {z | z.re = -(1 / 2)}) ∪ Metric.sphere 0 1 := by
    rintro _ ⟨τ, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
    by_cases hn : normSq (τ : ℂ) = 1
    · right
      rw [mem_sphere_zero_iff_norm]
      have h0 := norm_nonneg (τ : ℂ)
      have h1 := Complex.normSq_eq_norm_sq (τ : ℂ)
      nlinarith
    · left
      have hlt : 1 < normSq (τ : ℂ) := lt_of_le_of_ne h1 (Ne.symm hn)
      have hre : |τ.re| = 1 / 2 := by
        by_contra hne
        exact h3 ⟨hlt, lt_of_le_of_ne h2 hne⟩
      rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.mp hre with h | h
      · left; simpa using h
      · right; simpa using h
  exact measure_mono_null hsub (measure_union_null
    (measure_union_null (volume_re_eq _) (volume_re_eq _)) (Measure.addHaar_sphere volume 0 1))

/-! ### Counting translates of `𝒟` -/

instance : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
  inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))

instance : Countable SL(2, ℤ) :=
  inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})

instance : Countable 𝒮ℒ :=
  (MonoidHom.rangeRestrict_surjective (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)).countable

/-- The points whose orbit meets the boundary of `𝒟`: a null set. -/
def badSet : Set ℍ := ⋃ a : 𝒮ℒ, (fun σ ↦ (a : GL (Fin 2) ℝ) • σ) ⁻¹' (𝒟 \ 𝒟ᵒ)

lemma measurableSet_fd_diff_fdo : MeasurableSet (𝒟 \ 𝒟ᵒ) :=
  measurableSet_fd.diff isOpen_fdo.measurableSet

lemma measurableSet_badSet : MeasurableSet badSet :=
  MeasurableSet.iUnion fun _ ↦ measurableSet_fd_diff_fdo.preimage (measurable_const_smul _)

lemma volume_badSet : volume badSet = 0 :=
  measure_iUnion_null fun a ↦ by
    rw [(measurePreserving_smul (a : GL (Fin 2) ℝ) volume).measure_preimage
      measurableSet_fd_diff_fdo.nullMeasurableSet]
    exact volume_fd_diff_fdo

lemma mapGL_ne_mapGL_neg (γ : SL(2, ℤ)) :
    (mapGL ℝ γ : GL (Fin 2) ℝ) ≠ mapGL ℝ (-γ) := by
  intro h
  have h' : γ = -γ := mapGL_injective h
  have e : ∀ i j, (γ : Matrix (Fin 2) (Fin 2) ℤ) i j = 0 := fun i j ↦ by
    have := congrArg (fun g : SL(2, ℤ) ↦ (g : Matrix (Fin 2) (Fin 2) ℤ) i j) h'
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] at this
    omega
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two, e 0 0, e 0 1, e 1 0, e 1 1] at hdet
  simp at hdet

/-- Outside `badSet`, exactly two elements of `𝒮ℒ` (namely `± γ₀`) move `σ` into `𝒟`. -/
lemma tsum_indicator_fd_smul {σ : ℍ} (hσ : σ ∉ badSet) :
    ∑' a : 𝒮ℒ, Set.indicator 𝒟 (1 : ℍ → ℝ≥0∞) ((a : GL (Fin 2) ℝ) • σ) = 2 := by
  have hgood : ∀ a : 𝒮ℒ, (a : GL (Fin 2) ℝ) • σ ∈ 𝒟 → (a : GL (Fin 2) ℝ) • σ ∈ 𝒟ᵒ :=
    fun a ha ↦ by
      by_contra hn
      exact hσ (mem_iUnion.mpr ⟨a, ⟨ha, hn⟩⟩)
  obtain ⟨γ₀, hγ₀⟩ := exists_smul_mem_fd σ
  let a₀ : 𝒮ℒ := ⟨mapGL ℝ γ₀, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩
  let a₁ : 𝒮ℒ := ⟨mapGL ℝ (-γ₀), MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩
  have ha₀ : (a₀ : GL (Fin 2) ℝ) • σ = γ₀ • σ := rfl
  have ha₁ : (a₁ : GL (Fin 2) ℝ) • σ = γ₀ • σ := SL_neg_smul γ₀ σ
  have hne : a₀ ≠ a₁ := fun h ↦ mapGL_ne_mapGL_neg γ₀ (congrArg Subtype.val h)
  rw [tsum_eq_sum (s := {a₀, a₁}), Finset.sum_pair hne]
  · simp only [ha₀, ha₁, indicator_of_mem hγ₀, Pi.one_apply]
    norm_num
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
    refine indicator_of_notMem (fun hmem ↦ ?_) _
    obtain ⟨γ, hγ⟩ := a.2
    have hγa : a = ⟨mapGL ℝ γ, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩ := Subtype.ext hγ.symm
    have h1 : γ • σ ∈ 𝒟ᵒ := by
      have := hgood a hmem; rwa [hγa] at this
    have h0 : γ₀ • σ ∈ 𝒟ᵒ := hgood a₀ hγ₀
    have h2 : (γ * γ₀⁻¹) • (γ₀ • σ) ∈ 𝒟ᵒ := by rwa [← mul_smul, inv_mul_cancel_right]
    rcases eq_one_or_neg_one_of_mem_fdo_mem_fdo h0 h2 with h | h
    · exact ha.1 (hγa.trans (by rw [mul_inv_eq_one.mp h]))
    · have : γ = -γ₀ := by rw [mul_inv_eq_iff_eq_mul.mp h, neg_one_mul]
      exact ha.2 (hγa.trans (by rw [this]))

/-! ### Coset decomposition of `𝒮ℒ` -/

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)}

local notation "𝒬" => 𝒮ℒ ⧸ (𝒢.subgroupOf 𝒮ℒ)

/-- `𝒮ℒ ≃ (𝒮ℒ ⧸ 𝒢) × 𝒢` via `(q, γ) ↦ q.out * γ`. -/
def cosetProdEquiv : 𝒬 × ↥(𝒢.subgroupOf 𝒮ℒ) ≃ 𝒮ℒ where
  toFun p := p.1.out * p.2
  invFun a := (QuotientGroup.mk a, ⟨(QuotientGroup.mk a : 𝒬).out⁻¹ * a, by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (𝒢.subgroupOf 𝒮ℒ) a
    rw [hh, mul_inv_rev, inv_mul_cancel_right]
    exact inv_mem h.2⟩)
  left_inv p := by
    obtain ⟨q, s⟩ := p
    have hq : (QuotientGroup.mk (q.out * s) : 𝒬) = q := by
      rw [QuotientGroup.mk_mul_of_mem _ s.2, QuotientGroup.out_eq']
    ext
    · exact hq
    · simp only
      rw [hq, inv_mul_cancel_left]
  right_inv a := by simp

/-! ### Unfolding -/

variable [𝒢.IsArithmetic]

/-- The weight `R τ = ∑_q 𝟙_𝒟 (h_q τ)` attached to the representatives `h_q = q.out`. -/
def fdWeight (G : Subgroup (GL (Fin 2) ℝ)) [G.IsArithmetic] (τ : ℍ) : ℝ≥0∞ :=
  Finset.sum (@Finset.univ (𝒮ℒ ⧸ G.subgroupOf 𝒮ℒ) (Fintype.ofFinite _)) fun q ↦
    Set.indicator 𝒟 1 ((q.out : GL (Fin 2) ℝ) • τ)

lemma measurable_fdWeight : Measurable (fdWeight 𝒢) := by
  unfold fdWeight
  refine Finset.measurable_sum _ fun q _ ↦ ?_
  exact (measurable_one.indicator measurableSet_fd).comp (measurable_const_smul _)

/-- **Unfolding along `SL(2, ℤ)`**: `∫_𝒟 ∑_q v (h_q⁻¹ τ) = ∫_ℍ v · R`. -/
lemma lintegral_fd_sum_eq {v : ℍ → ℝ≥0∞} (hv : Measurable v) :
    ∫⁻ τ in 𝒟, (Finset.sum (@Finset.univ 𝒬 (Fintype.ofFinite 𝒬)) fun q ↦
      v ((q.out : GL (Fin 2) ℝ)⁻¹ • τ)) = ∫⁻ σ, v σ * fdWeight 𝒢 σ := by
  rw [lintegral_finsetSum]
  swap
  · intro q _; exact hv.comp (measurable_const_smul _)
  simp only [fdWeight, Finset.mul_sum]
  rw [lintegral_finsetSum]
  swap
  · intro q _
    exact hv.mul ((measurable_one.indicator measurableSet_fd).comp (measurable_const_smul _))
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  set h : GL (Fin 2) ℝ := ((q.out : 𝒮ℒ) : GL (Fin 2) ℝ)
  rw [← lintegral_indicator measurableSet_fd,
    ← (measurePreserving_smul h volume).lintegral_comp_emb (measurableEmbedding_const_smul h)]
  refine lintegral_congr fun σ ↦ ?_
  by_cases hσ : h • σ ∈ 𝒟
  · simp [indicator_of_mem hσ, inv_smul_smul]
  · simp [indicator_of_notMem hσ]

variable [𝒢.HasDetOne]

omit [𝒢.HasDetOne] in
/-- Summing the weight over `𝒢` counts all translates of `𝒟`: the sum is `2` off `badSet`. -/
lemma tsum_fdWeight_smul {σ : ℍ} (hσ : σ ∉ badSet) :
    ∑' s : ↥(𝒢.subgroupOf 𝒮ℒ), fdWeight 𝒢 ((s : GL (Fin 2) ℝ) • σ) = 2 := by
  let : Fintype 𝒬 := Fintype.ofFinite _
  have hw : ∀ τ, fdWeight 𝒢 τ = ∑ q : 𝒬, Set.indicator 𝒟 1 ((q.out : GL (Fin 2) ℝ) • τ) := by
    intro τ; simp only [fdWeight]
  simp_rw [hw]
  calc ∑' s : ↥(𝒢.subgroupOf 𝒮ℒ), ∑ q : 𝒬,
          Set.indicator 𝒟 (1 : ℍ → ℝ≥0∞) ((q.out : GL (Fin 2) ℝ) • (s : GL (Fin 2) ℝ) • σ)
      = ∑ q : 𝒬, ∑' s : ↥(𝒢.subgroupOf 𝒮ℒ),
          Set.indicator 𝒟 (1 : ℍ → ℝ≥0∞) ((q.out : GL (Fin 2) ℝ) • (s : GL (Fin 2) ℝ) • σ) :=
        Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable
    _ = ∑' q : 𝒬, ∑' s : ↥(𝒢.subgroupOf 𝒮ℒ),
          Set.indicator 𝒟 (1 : ℍ → ℝ≥0∞) ((q.out : GL (Fin 2) ℝ) • (s : GL (Fin 2) ℝ) • σ) :=
        (tsum_fintype _).symm
    _ = ∑' p : 𝒬 × ↥(𝒢.subgroupOf 𝒮ℒ),
          Set.indicator 𝒟 (1 : ℍ → ℝ≥0∞) ((cosetProdEquiv p : GL (Fin 2) ℝ) • σ) := by
        rw [ENNReal.tsum_prod']
        simp [cosetProdEquiv, mul_smul]
    _ = ∑' a : 𝒮ℒ, Set.indicator 𝒟 (1 : ℍ → ℝ≥0∞) ((a : GL (Fin 2) ℝ) • σ) :=
        cosetProdEquiv.tsum_eq (fun a : 𝒮ℒ ↦ Set.indicator 𝒟 (1 : ℍ → ℝ≥0∞) ((a : GL (Fin 2) ℝ) • σ))
    _ = 2 := tsum_indicator_fd_smul hσ

omit [𝒢.IsArithmetic] [𝒢.HasDetOne] in
/-- Two weights whose `𝒢`-sums are `2` almost everywhere integrate a `𝒢`-invariant function to
the same value. -/
lemma lintegral_mul_eq_of_tsum_eq_two {v R R' : ℍ → ℝ≥0∞} (hv : Measurable v)
    (hR : Measurable R) (hR' : Measurable R')
    (hinv : ∀ s : ↥(𝒢.subgroupOf 𝒮ℒ), ∀ τ, v ((s : GL (Fin 2) ℝ) • τ) = v τ)
    (hRs : ∀ᵐ σ, ∑' s : ↥(𝒢.subgroupOf 𝒮ℒ), R ((s : GL (Fin 2) ℝ) • σ) = 2)
    (hR's : ∀ᵐ σ, ∑' s : ↥(𝒢.subgroupOf 𝒮ℒ), R' ((s : GL (Fin 2) ℝ) • σ) = 2) :
    ∫⁻ τ, v τ * R τ = ∫⁻ τ, v τ * R' τ := by
  have key : ∀ A B : ℍ → ℝ≥0∞, Measurable A → Measurable B →
      (∀ᵐ σ, ∑' s : ↥(𝒢.subgroupOf 𝒮ℒ), B ((s : GL (Fin 2) ℝ) • σ) = 2) →
      2 * ∫⁻ τ, v τ * A τ = ∑' s : ↥(𝒢.subgroupOf 𝒮ℒ), ∫⁻ τ, v τ * A τ * B ((s : GL (Fin 2) ℝ) • τ) := by
    intro A B hA hB hBs
    rw [← lintegral_const_mul' _ _ (by norm_num)]
    calc ∫⁻ τ, 2 * (v τ * A τ)
        = ∫⁻ τ, ∑' s : ↥(𝒢.subgroupOf 𝒮ℒ), v τ * A τ * B ((s : GL (Fin 2) ℝ) • τ) := by
          refine lintegral_congr_ae (hBs.mono fun τ hτ ↦ ?_)
          simp only
          rw [ENNReal.tsum_mul_left, hτ, mul_comm]
      _ = ∑' s : ↥(𝒢.subgroupOf 𝒮ℒ), ∫⁻ τ, v τ * A τ * B ((s : GL (Fin 2) ℝ) • τ) :=
          lintegral_tsum fun s ↦
            ((hv.mul hA).mul (hB.comp (measurable_const_smul _))).aemeasurable
  have hsub : ∀ s : ↥(𝒢.subgroupOf 𝒮ℒ), ∫⁻ τ, v τ * R τ * R' ((s : GL (Fin 2) ℝ) • τ) =
      ∫⁻ σ, v σ * R ((s : GL (Fin 2) ℝ)⁻¹ • σ) * R' σ := by
    intro s
    rw [← (measurePreserving_smul ((s : GL (Fin 2) ℝ)⁻¹) volume).lintegral_comp_emb
      (measurableEmbedding_const_smul _)]
    refine lintegral_congr fun σ ↦ ?_
    have := hinv s⁻¹ σ
    simp only [InvMemClass.coe_inv, smul_inv_smul] at this ⊢
    rw [this]
  have h3 : ∑' s : ↥(𝒢.subgroupOf 𝒮ℒ), ∫⁻ τ, v τ * R τ * R' ((s : GL (Fin 2) ℝ) • τ) =
      ∑' s : ↥(𝒢.subgroupOf 𝒮ℒ), ∫⁻ τ, v τ * R' τ * R ((s : GL (Fin 2) ℝ) • τ) := by
    simp_rw [hsub]
    rw [← (Equiv.inv ↥(𝒢.subgroupOf 𝒮ℒ)).tsum_eq]
    refine tsum_congr fun s ↦ lintegral_congr fun σ ↦ ?_
    simp only [Equiv.inv_apply, InvMemClass.coe_inv, inv_inv]
    ring
  have h := (key R R' hR hR' hR's).trans (h3.trans (key R' R hR' hR hRs).symm)
  exact (ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top).mp h

/-- **Invariance of the unfolded integral** under a determinant-one matrix `W` normalizing
`𝒢 ≤ 𝒮ℒ`. -/
theorem lintegral_fd_sum_comp_smul (h𝒢 : 𝒢 ≤ 𝒮ℒ) (W : GL (Fin 2) ℝ)
    (hW : ∀ γ ∈ 𝒢, W⁻¹ * γ * W ∈ 𝒢) (hW' : ∀ γ ∈ 𝒢, W * γ * W⁻¹ ∈ 𝒢)
    {v : ℍ → ℝ≥0∞} (hv : Measurable v) (hinv : ∀ γ ∈ 𝒢, ∀ τ, v (γ • τ) = v τ) :
    ∫⁻ τ in 𝒟, (Finset.sum (@Finset.univ 𝒬 (Fintype.ofFinite 𝒬)) fun q ↦
      v (W • (q.out : GL (Fin 2) ℝ)⁻¹ • τ)) =
    ∫⁻ τ in 𝒟, (Finset.sum (@Finset.univ 𝒬 (Fintype.ofFinite 𝒬)) fun q ↦
      v ((q.out : GL (Fin 2) ℝ)⁻¹ • τ)) := by
  have hvW : Measurable fun x ↦ v (W • x) := hv.comp (measurable_const_smul _)
  rw [lintegral_fd_sum_eq (𝒢 := 𝒢) hvW, lintegral_fd_sum_eq (𝒢 := 𝒢) hv]
  -- change variables `σ = W⁻¹ ρ`
  rw [← (measurePreserving_smul W⁻¹ volume).lintegral_comp_emb (measurableEmbedding_const_smul _)]
  simp only [smul_inv_smul]
  symm
  refine lintegral_mul_eq_of_tsum_eq_two hv measurable_fdWeight
    (measurable_fdWeight.comp (measurable_const_smul _)) (fun s τ ↦ hinv _ s.2 τ) ?_ ?_
  · exact (measure_eq_zero_iff_ae_notMem.mp volume_badSet).mono fun σ hσ ↦
      tsum_fdWeight_smul hσ
  · -- the conjugate weight
    have hnull : volume ((fun σ ↦ W⁻¹ • σ) ⁻¹' badSet) = 0 := by
      rw [(measurePreserving_smul W⁻¹ volume).measure_preimage
        measurableSet_badSet.nullMeasurableSet]
      exact volume_badSet
    refine (measure_eq_zero_iff_ae_notMem.mp hnull).mono fun σ hσ ↦ ?_
    let e : ↥(𝒢.subgroupOf 𝒮ℒ) ≃ ↥(𝒢.subgroupOf 𝒮ℒ) :=
      { toFun s := ⟨⟨W⁻¹ * s * W, h𝒢 (hW _ s.2)⟩, hW _ s.2⟩
        invFun s := ⟨⟨W * s * W⁻¹, h𝒢 (hW' _ s.2)⟩, hW' _ s.2⟩
        left_inv s := by ext; simp [mul_assoc]
        right_inv s := by ext; simp [mul_assoc] }
    have hσ' : W⁻¹ • σ ∉ badSet := hσ
    rw [← tsum_fdWeight_smul (𝒢 := 𝒢) hσ',
      ← e.tsum_eq (fun s : ↥(𝒢.subgroupOf 𝒮ℒ) ↦ fdWeight 𝒢 ((s : GL (Fin 2) ℝ) • W⁻¹ • σ))]
    refine tsum_congr fun s ↦ ?_
    simp [e, mul_smul]

/-! ### Invariance of the Petersson inner product -/

variable {k : ℤ}

lemma ofReal_peterssonSum_self_re (f : CuspForm 𝒢 k) (τ : ℍ) :
    ENNReal.ofReal (peterssonSum f f τ).re =
      Finset.sum (@Finset.univ 𝒬 (Fintype.ofFinite 𝒬)) fun q ↦
        ENNReal.ofReal (‖f ((q.out : GL (Fin 2) ℝ)⁻¹ • τ)‖ ^ 2 *
          ((q.out : GL (Fin 2) ℝ)⁻¹ • τ).im ^ k) := by
  rw [peterssonSum, re_sum, ENNReal.ofReal_sum_of_nonneg fun q _ ↦
    peterssonTerm_self_re_nonneg f q τ]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [peterssonTerm, petersson_self_eq, ofReal_re]

lemma integral_peterssonSum_self_re (f : CuspForm 𝒢 k) :
    ∫ τ in 𝒟, (peterssonSum f f τ).re =
      (∫⁻ τ in 𝒟, ENNReal.ofReal (peterssonSum f f τ).re).toReal :=
  integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun τ ↦ peterssonSum_self_re_nonneg f τ)
    (continuous_re.comp (continuous_peterssonSum f f)).aestronglyMeasurable

/-- `⟪f ∣ W, f ∣ W⟫ = ⟪f, f⟫` for `W` of determinant one normalizing `𝒢 ≤ 𝒮ℒ`. -/
theorem peterssonInner_self_slash (h𝒢 : 𝒢 ≤ 𝒮ℒ) (W : GL (Fin 2) ℝ) (hdet : W.det = 1)
    (hW : ∀ γ ∈ 𝒢, W⁻¹ * γ * W ∈ 𝒢) (hW' : ∀ γ ∈ 𝒢, W * γ * W⁻¹ ∈ 𝒢)
    (f fW : CuspForm 𝒢 k) (hfW : ⇑fW = ⇑f ∣[k] W) :
    peterssonInner fW fW = peterssonInner f f := by
  rw [peterssonInner_self_eq, peterssonInner_self_eq, integral_peterssonSum_self_re,
    integral_peterssonSum_self_re]
  congr 2
  set v : ℍ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (‖f x‖ ^ 2 * x.im ^ k) with hv_def
  have hv : Measurable v := by
    refine Measurable.ennreal_ofReal (Continuous.measurable ?_)
    have := (ModularFormClass.holo f).continuous
    fun_prop (disch := simp [UpperHalfPlane.im_ne_zero _])
  have hdet' : (W.det : ℝ) = 1 := by rw [hdet]; rfl
  have hvW : ∀ x, ENNReal.ofReal (‖fW x‖ ^ 2 * x.im ^ k) = v (W • x) := by
    intro x
    have h := petersson_slash k f f W x
    rw [← hfW, hdet', abs_one, Complex.ofReal_one, one_zpow, one_mul] at h
    have hσ : σ W = ContinuousAlgEquiv.refl ℝ ℂ := by simp [σ, hdet']
    rw [hσ, petersson_self_eq, petersson_self_eq] at h
    simp only [ContinuousAlgEquiv.refl_apply, ofReal_inj] at h
    rw [h]
  have hinv : ∀ γ ∈ 𝒢, ∀ x, v (γ • x) = v x := by
    intro γ hγ x
    have h := SlashInvariantFormClass.petersson_smul (f := f) (f' := f) (τ := x) hγ
    rw [petersson_self_eq, petersson_self_eq, ofReal_inj] at h
    simp only [hv_def, h]
  simp_rw [ofReal_peterssonSum_self_re, hvW]
  exact lintegral_fd_sum_comp_smul h𝒢 W hW hW' hv hinv

/-- Polarization for the Petersson inner product. -/
lemma peterssonInner_polarization (x y : CuspForm 𝒢 k) :
    4 * peterssonInner x y =
      peterssonInner (x + y) (x + y) - peterssonInner (x + (-1 : ℂ) • y) (x + (-1 : ℂ) • y) -
      Complex.I * (peterssonInner (x + Complex.I • y) (x + Complex.I • y) -
        peterssonInner (x + (-Complex.I) • y) (x + (-Complex.I) • y)) := by
  have hexp : ∀ c : ℂ, peterssonInner (x + c • y) (x + c • y) =
      peterssonInner x x + c * peterssonInner x y + conj c * peterssonInner y x +
        conj c * c * peterssonInner y y := by
    intro c
    rw [peterssonInner_add_left, peterssonInner_add_right, peterssonInner_add_right,
      peterssonInner_smul_left, peterssonInner_smul_left, peterssonInner_smul_right,
      peterssonInner_smul_right]
    ring
  have h1 := hexp 1
  simp only [one_smul, map_one, one_mul] at h1
  rw [h1, hexp (-1), hexp Complex.I, hexp (-Complex.I)]
  simp only [map_neg, map_one, conj_I]
  linear_combination (2 * peterssonInner x y - 2 * peterssonInner y x) * I_sq

/-- A linear map preserving `⟪f, f⟫` preserves the Petersson inner product. -/
lemma peterssonInner_map_eq (L : CuspForm 𝒢 k →ₗ[ℂ] CuspForm 𝒢 k)
    (hL : ∀ f, peterssonInner (L f) (L f) = peterssonInner f f) (f g : CuspForm 𝒢 k) :
    peterssonInner (L f) (L g) = peterssonInner f g := by
  have h := peterssonInner_polarization (L f) (L g)
  simp only [← map_smul, ← map_add, hL] at h
  rw [← peterssonInner_polarization] at h
  exact (mul_right_inj' (by norm_num : (4 : ℂ) ≠ 0)).mp h

end PilotF
