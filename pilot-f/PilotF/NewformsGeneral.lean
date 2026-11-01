/-
Copyright (c) 2026 Liam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liam
-/
import PilotF.Newforms

/-!
# Newforms are the Petersson complement of oldforms, at every level

We prove `NewSubspaceEqOrthogonal N k` for every `N ≠ 0`: Pilot D's trace-kernel new subspace
of `S_k(Γ₀(N))` is the Petersson orthogonal complement of the old subspace.

The proof, for each prime `p ∣ N` with `M = N / p`:

* the old subspace is spanned by `B_1 (S_k(Γ₀(M)))` and `B_p (S_k(Γ₀(M)))` over primes `p ∣ N`,
  since every `B_d` from a level `M' < N` factors through one of them
  (`levelRaise_mul_apply`);
* the trace `Tr_{N/M}` is adjoint to the inclusion `B_1`
  (`peterssonInner_eq_peterssonInner_trace_of_le`, an unfolding along the cosets of
  `Γ₀(N) ≤ Γ₀(M) ≤ SL(2, ℤ)`);
* `B_p = (-√p) ^ (-k) • W_N ∘ B_1 ∘ W_M` (`levelRaise_p_eq_smul_fricke`), and `W_N` is
  self-adjoint while `W_M` is a bijection of `S_k(Γ₀(M))`.

Only the Fricke involutions `W_N`, `W_M` appear (Pilot D's `newSubspace` uses only `W_N`), so the
general Atkin–Lehner operators `W_Q` for `Q ∥ N` are not needed.
-/

open UpperHalfPlane ModularGroup MeasureTheory Complex Set CongruenceSubgroup
open scoped MatrixGroups ComplexConjugate ModularForm Modular Manifold

noncomputable section

namespace PilotF

variable {k : ℤ}

/-! ### The trace is adjoint to the inclusion, for `𝒢 ≤ ℋ ≤ 𝒮ℒ` -/

section TraceAdjoint

variable {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)}

/-- The coset map `(a ℋ, b 𝒢) ↦ a b 𝒢` from `(𝒮ℒ ⧸ ℋ) × (ℋ ⧸ 𝒢)` to `𝒮ℒ ⧸ 𝒢`. -/
def cosetMul (hℋ : ℋ ≤ 𝒮ℒ)
    (x : (𝒮ℒ ⧸ ℋ.subgroupOf 𝒮ℒ) × (ℋ ⧸ 𝒢.subgroupOf ℋ)) : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ :=
  QuotientGroup.mk (⟨(x.1.out : GL (Fin 2) ℝ) * (x.2.out : GL (Fin 2) ℝ),
    mul_mem x.1.out.2 (hℋ x.2.out.2)⟩ : 𝒮ℒ)

lemma cosetMul_bijective (h𝒢ℋ : 𝒢 ≤ ℋ) (hℋ : ℋ ≤ 𝒮ℒ) :
    Function.Bijective (cosetMul (𝒢 := 𝒢) hℋ) := by
  constructor
  · rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 := QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf] at h1
    simp only [InvMemClass.coe_inv, MulMemClass.coe_mul] at h1
    set A : GL (Fin 2) ℝ := (a.out : GL (Fin 2) ℝ)
    set A' : GL (Fin 2) ℝ := (a'.out : GL (Fin 2) ℝ)
    set B : GL (Fin 2) ℝ := (b.out : GL (Fin 2) ℝ)
    set B' : GL (Fin 2) ℝ := (b'.out : GL (Fin 2) ℝ)
    have hB : B ∈ ℋ := b.out.2
    have hB' : B' ∈ ℋ := b'.out.2
    have ha : a = a' := by
      rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' a']
      refine QuotientGroup.eq.mpr ?_
      rw [Subgroup.mem_subgroupOf]
      have e : A⁻¹ * A' = B * ((A * B)⁻¹ * (A' * B')) * B'⁻¹ := by group
      simp only [InvMemClass.coe_inv, MulMemClass.coe_mul]
      rw [e]
      exact mul_mem (mul_mem hB (h𝒢ℋ h1)) (inv_mem hB')
    subst ha
    have hb : b = b' := by
      rw [← QuotientGroup.out_eq' b, ← QuotientGroup.out_eq' b']
      refine QuotientGroup.eq.mpr ?_
      rw [Subgroup.mem_subgroupOf]
      have e : B⁻¹ * B' = (A * B)⁻¹ * (A * B') := by group
      simp only [InvMemClass.coe_inv, MulMemClass.coe_mul]
      rw [e]
      exact h1
    rw [hb]
  · intro q
    set x : 𝒮ℒ := q.out
    set a : 𝒮ℒ ⧸ ℋ.subgroupOf 𝒮ℒ := QuotientGroup.mk x
    have hy : ((a.out : GL (Fin 2) ℝ))⁻¹ * (x : GL (Fin 2) ℝ) ∈ ℋ := by
      have := QuotientGroup.eq.mp (QuotientGroup.out_eq' a)
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    set b : ℋ ⧸ 𝒢.subgroupOf ℋ := QuotientGroup.mk (⟨_, hy⟩ : ℋ)
    refine ⟨(a, b), ?_⟩
    rw [← QuotientGroup.out_eq' q]
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    have hb := QuotientGroup.eq.mp (QuotientGroup.out_eq' b)
    rw [Subgroup.mem_subgroupOf] at hb
    simp only [InvMemClass.coe_inv, MulMemClass.coe_mul] at hb ⊢
    have e : ((a.out : GL (Fin 2) ℝ) * (b.out : GL (Fin 2) ℝ))⁻¹ * (x : GL (Fin 2) ℝ) =
        (b.out : GL (Fin 2) ℝ)⁻¹ * ((a.out : GL (Fin 2) ℝ)⁻¹ * (x : GL (Fin 2) ℝ)) := by group
    rw [e]
    exact hb

variable [𝒢.IsArithmetic] [𝒢.HasDetOne] [ℋ.IsArithmetic] [ℋ.HasDetOne]

omit [ℋ.IsArithmetic] in
/-- For `G` invariant under `ℋ` and `h ∈ ℋ` of determinant one,
`petersson k G (F ∣ h⁻¹) τ = petersson k G F (h⁻¹ τ)`. -/
lemma petersson_slash_inv_of_mem (G : CuspForm ℋ k) (F : ℍ → ℂ) {h : GL (Fin 2) ℝ}
    (hh : h ∈ ℋ) (τ : ℍ) :
    petersson k G (F ∣[k] h⁻¹) τ = petersson k G F (h⁻¹ • τ) := by
  have hdet : ((h⁻¹).det : ℝ) = 1 := by
    rw [Subgroup.HasDetOne.det_eq (inv_mem hh)]; rfl
  have hdetA : (h.det : ℝ) = 1 := by
    rw [Subgroup.HasDetOne.det_eq hh]; rfl
  have hσ : σ h⁻¹ = ContinuousAlgEquiv.refl ℝ ℂ := by simp [σ, hdetA]
  have e := petersson_slash k G F h⁻¹ τ
  rw [hdet, abs_one, Complex.ofReal_one, one_zpow, one_mul, hσ,
    ContinuousAlgEquiv.refl_apply, SlashInvariantFormClass.slash_action_eq G _ (inv_mem hh)] at e
  exact e

/-- **Trace adjointness**: for `𝒢 ≤ ℋ ≤ 𝒮ℒ` and `G` on `ℋ`, the Petersson integrand of `G` and
`f` on `𝒢` equals the integrand of `G` and `Tr f` on `ℋ`. -/
lemma peterssonSum_eq_peterssonSum_trace (h𝒢ℋ : 𝒢 ≤ ℋ) (hℋ : ℋ ≤ 𝒮ℒ)
    [𝒢.IsFiniteRelIndex ℋ] (G : CuspForm ℋ k) (g f : CuspForm 𝒢 k) (hg : ⇑g = ⇑G) (τ : ℍ) :
    peterssonSum g f τ = peterssonSum G (CuspForm.trace ℋ f) τ := by
  let : Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) := Fintype.ofFinite _
  let : Fintype (𝒮ℒ ⧸ ℋ.subgroupOf 𝒮ℒ) := Fintype.ofFinite _
  let : Fintype (ℋ ⧸ 𝒢.subgroupOf ℋ) := Fintype.ofFinite _
  rw [peterssonSum_eq, peterssonSum_eq]
  symm
  calc ∑ a : 𝒮ℒ ⧸ ℋ.subgroupOf 𝒮ℒ, peterssonTerm G (CuspForm.trace ℋ f) a τ
      = ∑ a : 𝒮ℒ ⧸ ℋ.subgroupOf 𝒮ℒ, ∑ b : ℋ ⧸ 𝒢.subgroupOf ℋ,
          peterssonTerm g f (cosetMul hℋ (a, b)) τ := by
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [peterssonTerm, CuspForm.coe_trace]
        simp only [petersson, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        rw [cosetMul, peterssonTerm_mk, ← QuotientGroup.out_eq' b,
          SlashInvariantForm.quotientFunc_mk, QuotientGroup.out_eq']
        have e := petersson_slash_inv_of_mem G (⇑f) b.out.2 ((a.out : GL (Fin 2) ℝ)⁻¹ • τ)
        rw [hg, mul_inv_rev, mul_smul]
        exact e
    _ = ∑ x : (𝒮ℒ ⧸ ℋ.subgroupOf 𝒮ℒ) × (ℋ ⧸ 𝒢.subgroupOf ℋ),
          peterssonTerm g f (cosetMul hℋ x) τ :=
        (Fintype.sum_prod_type (fun x ↦ peterssonTerm g f (cosetMul hℋ x) τ)).symm
    _ = ∑ q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ, peterssonTerm g f q τ :=
        Fintype.sum_bijective (cosetMul hℋ) (cosetMul_bijective h𝒢ℋ hℋ)
          (fun x ↦ peterssonTerm g f (cosetMul hℋ x) τ) (fun q ↦ peterssonTerm g f q τ)
          fun _ ↦ rfl

theorem peterssonInner_eq_peterssonInner_trace_of_le (h𝒢ℋ : 𝒢 ≤ ℋ) (hℋ : ℋ ≤ 𝒮ℒ)
    [𝒢.IsFiniteRelIndex ℋ] (G : CuspForm ℋ k) (g f : CuspForm 𝒢 k) (hg : ⇑g = ⇑G) :
    peterssonInner g f = peterssonInner G (CuspForm.trace ℋ f) := by
  simp only [peterssonInner, peterssonSum_eq_peterssonSum_trace h𝒢ℋ hℋ G g f hg]

end TraceAdjoint

/-! ### Level raising and the Fricke involution -/

lemma levelRaise_mul_apply {M d₁ d₂ d L N : ℕ} [NeZero d₁] [NeZero d₂] [NeZero d]
    (hd : d = d₁ * d₂) (h : M * d ∣ N) (h₁ : M * d₁ ∣ L) (h₂ : L * d₂ ∣ N)
    (g : CuspForm (Gamma0 M) k) :
    CuspForm.levelRaise M d N h g =
      CuspForm.levelRaise L d₂ N h₂ (CuspForm.levelRaise M d₁ L h₁ g) := by
  ext τ
  rw [CuspForm.levelRaise_apply, CuspForm.levelRaise_apply, CuspForm.levelRaise_apply]
  congr 1
  ext
  simp only [CuspForm.coe_levelRaiseMatrix_smul, hd]
  push_cast
  ring

lemma cuspForm_fricke_apply (N : ℕ) [NeZero N] (f : CuspForm (Gamma0 N) k) (τ : ℍ) :
    CuspForm.fricke N f τ = (√(N : ℝ) * (τ : ℂ)) ^ (-k) * f (frickeMatrix N • τ) := by
  have hsR : √(N : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
  rw [CuspForm.coe_fricke, ModularForm.slash_apply]
  simp [σ, denom, coe_frickeMatrix, hsR]
  ring

lemma frickeMatrix_smul_frickeMatrix_smul {M p N : ℕ} [NeZero M] [NeZero p] [NeZero N]
    (hN : N = M * p) (τ : ℍ) :
    frickeMatrix M • frickeMatrix N • τ = levelRaiseMatrix p • τ := by
  ext
  rw [ModularForm.coe_frickeMatrix_smul, ModularForm.coe_frickeMatrix_smul,
    CuspForm.coe_levelRaiseMatrix_smul, hN]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  push_cast
  field_simp

/-- `B_p g = (-√p) ^ (-k) • W_N (B_1 (W_M g))` for `N = M p`. -/
lemma levelRaise_p_eq_smul_fricke {M p N : ℕ} [NeZero M] [NeZero p] [NeZero N]
    (hN : N = M * p) (h1 : M * 1 ∣ N) (hp : M * p ∣ N) (g : CuspForm (Gamma0 M) k) :
    CuspForm.levelRaise M p N hp g = ((-√(p : ℝ) : ℂ) ^ (-k)) •
      CuspForm.fricke N (CuspForm.levelRaise M 1 N h1 (CuspForm.fricke M g)) := by
  ext τ
  have hB1 : ∀ F : CuspForm (Gamma0 M) k, ⇑(CuspForm.levelRaise M 1 N h1 F) = ⇑F := by
    intro F
    funext σ'
    rw [CuspForm.levelRaise_apply]
    congr 1
    ext
    simp [CuspForm.coe_levelRaiseMatrix_smul]
  rw [smul_apply, smul_eq_mul, cuspForm_fricke_apply, hB1, cuspForm_fricke_apply,
    frickeMatrix_smul_frickeMatrix_smul hN, CuspForm.levelRaise_apply,
    ModularForm.coe_frickeMatrix_smul]
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hpR : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hMR : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hsp : (√(p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hpR).ne'
  have hsM : (√(M : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hMR).ne'
  have hsN : (√(N : ℝ) : ℂ) = √(M : ℝ) * √(p : ℝ) := by
    rw [hN]; push_cast; exact_mod_cast Real.sqrt_mul hMR.le p
  have hp2 : (√(p : ℝ) : ℂ) * √(p : ℝ) = p := by
    exact_mod_cast Real.mul_self_sqrt hpR.le
  have hM2 : (√(M : ℝ) : ℂ) * √(M : ℝ) = M := by exact_mod_cast Real.mul_self_sqrt hMR.le
  have hNC : (N : ℂ) = √(M : ℝ) * √(M : ℝ) * (√(p : ℝ) * √(p : ℝ)) := by
    rw [hM2, hp2, hN]; push_cast; ring
  -- the scalar: `(√N τ) * (√M * (-1 / (N τ))) = -1 / √p`
  have key : (√(N : ℝ) * (τ : ℂ)) * (√(M : ℝ) * (-1 / ((N : ℂ) * τ))) = (-√(p : ℝ) : ℂ)⁻¹ := by
    rw [hsN, hNC]
    field_simp
  have hk : (-√(p : ℝ) : ℂ) ^ (-k) * ((√(N : ℝ) * (τ : ℂ)) ^ (-k) *
      ((√(M : ℝ) : ℂ) * (-1 / ((N : ℂ) * τ))) ^ (-k)) = 1 := by
    rw [← mul_zpow, key, inv_zpow', neg_neg, ← zpow_add₀ (neg_ne_zero.mpr hsp), neg_add_cancel,
      zpow_zero]
  calc g (levelRaiseMatrix p • τ)
      = ((-√(p : ℝ) : ℂ) ^ (-k) * ((√(N : ℝ) * (τ : ℂ)) ^ (-k) *
        ((√(M : ℝ) : ℂ) * (-1 / ((N : ℂ) * τ))) ^ (-k))) * g (levelRaiseMatrix p • τ) := by
        rw [hk, one_mul]
    _ = _ := by ring

/-! ### The main theorem -/

lemma traceₗ_eq_zero_iff_forall {M N : ℕ} [NeZero M] [NeZero N] (h : M * 1 ∣ N)
    (f : CuspForm (Gamma0 N) k) :
    (∀ g : CuspForm (Gamma0 M) k, peterssonInner (CuspForm.levelRaise M 1 N h g) f = 0) ↔
      CuspForm.traceₗ M N f = 0 := by
  have hMN : M ∣ N := by simpa using h
  have hB1 : ∀ F : CuspForm (Gamma0 M) k, ⇑(CuspForm.levelRaise M 1 N h F) = ⇑F := by
    intro F
    funext σ'
    rw [CuspForm.levelRaise_apply]
    congr 1
    ext
    simp [CuspForm.coe_levelRaiseMatrix_smul]
  have hadj : ∀ g : CuspForm (Gamma0 M) k, peterssonInner (CuspForm.levelRaise M 1 N h g) f =
      peterssonInner g (CuspForm.traceₗ M N f) := fun g ↦
    peterssonInner_eq_peterssonInner_trace_of_le (Gamma0_le_Gamma0_GL hMN) (Gamma0_le_SL M) g
      _ f (hB1 g)
  simp only [hadj]
  exact forall_peterssonInner_eq_zero_iff _

/-- **Newforms are the Petersson complement of oldforms**, at every level `N ≠ 0`. -/
theorem newSubspaceEqOrthogonal (N : ℕ) [NeZero N] : NewSubspaceEqOrthogonal N k := by
  unfold NewSubspaceEqOrthogonal
  ext f
  rw [CuspForm.newSubspace, CuspForm.oldSubspace, mem_peterssonOrthogonal_iSup]
  simp only [Submodule.mem_iInf, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.coe_comp,
    Function.comp_apply]
  -- the two conditions at a prime `p ∣ N`, with `M = N / p`
  have hprime : ∀ p [NeZero p], p.Prime → p ∣ N →
      ∃ (_ : NeZero (N / p)) (h1 : N / p * 1 ∣ N) (hp : N / p * p ∣ N),
        ((∀ g : CuspForm (Gamma0 (N / p)) k,
          peterssonInner (CuspForm.levelRaise (N / p) 1 N h1 g) f = 0) ↔
            CuspForm.traceₗ (N / p) N f = 0) ∧
        ((∀ g : CuspForm (Gamma0 (N / p)) k,
          peterssonInner (CuspForm.levelRaise (N / p) p N hp g) f = 0) ↔
            CuspForm.traceₗ (N / p) N (CuspForm.fricke N f) = 0) := by
    intro p _ hp hpN
    have hN0 : N ≠ 0 := NeZero.ne N
    have hM0 : N / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hpN)
      hp.pos).ne'
    have : NeZero (N / p) := ⟨hM0⟩
    have hNp : N = N / p * p := (Nat.div_mul_cancel hpN).symm
    have h1 : N / p * 1 ∣ N := by rw [mul_one]; exact Nat.div_dvd_of_dvd hpN
    have hpp : N / p * p ∣ N := by rw [← hNp]
    refine ⟨inferInstance, h1, hpp, traceₗ_eq_zero_iff_forall h1 f, ?_⟩
    rw [← traceₗ_eq_zero_iff_forall h1]
    have hs : (√(p : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < p := by exact_mod_cast hp.pos
      exact_mod_cast (Real.sqrt_pos.mpr this).ne'
    have hc : conj ((-√(p : ℝ) : ℂ) ^ (-k)) ≠ 0 := by
      rw [map_ne_zero]
      exact zpow_ne_zero _ (neg_ne_zero.mpr hs)
    constructor
    · intro h g
      have := h (CuspForm.fricke (N / p) g)
      rw [levelRaise_p_eq_smul_fricke hNp h1 hpp, peterssonInner_smul_left,
        peterssonInner_fricke_left, CuspForm.fricke_fricke, mul_eq_zero, or_iff_right hc] at this
      exact this
    · intro h g
      rw [levelRaise_p_eq_smul_fricke hNp h1 hpp, peterssonInner_smul_left,
        peterssonInner_fricke_left, h, mul_zero]
  constructor
  · -- trace conditions imply orthogonality to every `B_d`
    rintro hnew ⟨⟨M', d⟩, hdvd, hlt⟩ _ ⟨g₀, rfl⟩
    simp only at hdvd hlt
    obtain ⟨e, he⟩ := hdvd
    have hd0 : d ≠ 0 := by rintro rfl; simp [NeZero.ne N] at he
    have hM'0 : M' ≠ 0 := by rintro rfl; simp [NeZero.ne N] at he
    have hde : d * e ≠ 1 := by
      intro h1
      rw [mul_assoc, h1, mul_one] at he
      omega
    obtain ⟨p, hp, hpde⟩ := Nat.exists_prime_and_dvd hde
    have hpN : p ∣ N := by rw [he, mul_assoc]; exact Dvd.dvd.mul_left hpde M'
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨_, h1, hpp, hA, hB⟩ := hprime p hp hpN
    have hpmem : p ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpN, NeZero.ne N⟩
    obtain ⟨hTr, hTrW⟩ := hnew p hpmem
    have hNp : N / p * p = N := Nat.div_mul_cancel hpN
    by_cases hpd : p ∣ d
    · -- `B_d = B_p ∘ B_{d / p}`
      obtain ⟨d', rfl⟩ := hpd
      have : NeZero d' := ⟨right_ne_zero_of_mul hd0⟩
      have hMd' : M' * d' ∣ N / p := by
        exact ⟨e, Nat.div_eq_of_eq_mul_left hp.pos (by rw [he]; ring)⟩
      rw [levelRaise_mul_apply (d₁ := d') (d₂ := p) (L := N / p) (mul_comm _ _) _ hMd' hpp]
      exact hB.mpr hTrW _
    · -- `B_d` lands in level `N / p`
      have hpe : p ∣ e := (Nat.Prime.dvd_mul hp).mp hpde |>.resolve_left hpd
      obtain ⟨e', rfl⟩ := hpe
      have hMd : M' * d ∣ N / p := by
        exact ⟨e', Nat.div_eq_of_eq_mul_left hp.pos (by rw [he]; ring)⟩
      have : NeZero d := ⟨hd0⟩
      rw [levelRaise_mul_apply (d₁ := d) (d₂ := 1) (L := N / p) (mul_one _).symm _ hMd h1]
      exact hA.mpr hTr _
  · -- orthogonality to the generators `B_1`, `B_p` from level `N / p` gives the trace conditions
    intro horth p hpmem
    obtain ⟨hp, hpN, -⟩ := Nat.mem_primeFactors.mp hpmem
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨_, h1, hpp, hA, hB⟩ := hprime p hp hpN
    have hlt : N / p < N := Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne N)) hp.one_lt
    exact ⟨hA.mp fun g ↦ horth ⟨(N / p, 1), h1, hlt⟩ _ ⟨g, rfl⟩,
      hB.mp fun g ↦ horth ⟨(N / p, p), hpp, hlt⟩ _ ⟨g, rfl⟩⟩

/-- For every `N ≠ 0`, `S_k^new(Γ₀(N))` (traces) is the Petersson complement of the old space. -/
theorem newSubspace_eq_peterssonOrthogonal (N : ℕ) [NeZero N] :
    CuspForm.newSubspace N k = peterssonOrthogonal (CuspForm.oldSubspace N k) :=
  newSubspaceEqOrthogonal N

end PilotF
