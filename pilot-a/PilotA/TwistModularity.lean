/-
Pilot A, milestone 3, steps 1 and 6 (see `BLUEPRINT.md` §4): `TwistStatement` is a theorem.

* The normalized twist `g(χ)⁻¹ · Σ_a χ(a) f(τ + a/D)` of a normalized eigenform `f` on `Γ₀(N)` by a
  primitive real character `χ` mod `D` is a normalized eigenform on `Γ₀(N D²)` with coefficients
  `χ(n) aₙ`.
* Primitive real characters exist for `d = -1` (`χ₄`), `d = 2` (`χ₈`) and `d = q* = χ₄(q) q`
  (the Legendre character mod an odd prime `q`).
* The twisting property is closed under products, which reaches every nonzero integer.
-/
import PilotA.Twist
import PilotA.TwistCoeffs
import PilotA.TwistQExpansion
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.Data.Nat.Factorization.Induction

set_option autoImplicit false

noncomputable section

namespace PilotA

open CongruenceSubgroup ModularForm ModularFormClass
open UpperHalfPlane hiding I
open Complex

/-! ### The normalized twist -/

section Normalized

variable {D : ℕ} [NeZero D]

omit [NeZero D] in
/-- A real character is its own inverse. -/
lemma inv_eq_self_of_sq (χ : DirichletCharacter ℂ D) (hχ2 : ∀ u : (ZMod D)ˣ, χ u ^ 2 = 1) :
    χ⁻¹ = χ := by
  refine MulChar.ext fun u => ?_
  rw [MulChar.inv_apply_eq_inv']
  exact inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hχ2 u)

/-- The normalized twist `g(χ)⁻¹ • f ⊗ χ`. -/
def normTwist (N : ℕ) [NeZero N] (f : CuspForm (Gamma0 N) 2) (χ : DirichletCharacter ℂ D)
    (hχ2 : ∀ u : (ZMod D)ˣ, χ u ^ 2 = 1) : CuspForm (Gamma0 (N * D ^ 2)) 2 :=
  (gaussSum χ ZMod.stdAddChar)⁻¹ • twistCuspForm N f χ hχ2

lemma qCoeff_normTwist (N : ℕ) [NeZero N] (f : CuspForm (Gamma0 N) 2)
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsPrimitive) (hχ2 : ∀ u : (ZMod D)ˣ, χ u ^ 2 = 1)
    (m : ℕ) : qCoeff (normTwist N f χ hχ2) m = χ (m : ZMod D) * qCoeff f m := by
  have hg := gaussSum_ne_zero_of_isPrimitive χ hχ
  have hinv := inv_eq_self_of_sq χ hχ2
  have key : ∀ τ : ℍ, HasSum (fun m : ℕ ↦ (χ (m : ZMod D) * (qExpansion 1 f).coeff m) •
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (normTwist N f χ hχ2 τ) := fun τ => by
    have := (hasSum_twistFun N f χ hχ τ).mul_left (gaussSum χ ZMod.stdAddChar)⁻¹
    have e1 : normTwist N f χ hχ2 τ = (gaussSum χ ZMod.stdAddChar)⁻¹ * twistFun f χ τ := rfl
    have e2 : (fun m : ℕ ↦ (χ (m : ZMod D) * (qExpansion 1 f).coeff m) •
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) = fun m : ℕ ↦ (gaussSum χ ZMod.stdAddChar)⁻¹ *
        ((gaussSum χ ZMod.stdAddChar * χ⁻¹ (m : ZMod D) * (qExpansion 1 f).coeff m) •
          Function.Periodic.qParam 1 (τ : ℂ) ^ m) := by
      funext m
      rw [hinv]
      simp only [smul_eq_mul]
      field_simp
    rw [e1, e2]
    exact this
  exact (ModularFormClass.qExpansion_coeff_unique (f := normTwist N f χ hχ2)
    (c := fun m : ℕ ↦ χ (m : ZMod D) * (qExpansion 1 f).coeff m)
    one_pos (one_mem_strictPeriods_Gamma0 _) key m).symm

/-- **Twisting a normalized eigenform by a primitive real character.** -/
theorem isNormalizedEigenform_normTwist (N : ℕ) [NeZero N] (f : CuspForm (Gamma0 N) 2)
    (hf : f.IsNormalizedEigenform) (χ : DirichletCharacter ℂ D) (hχ : χ.IsPrimitive)
    (hχ2 : ∀ u : (ZMod D)ˣ, χ u ^ 2 = 1) : (normTwist N f χ hχ2).IsNormalizedEigenform := by
  rw [isNormalizedEigenform_iff]
  have hc : qCoeff (normTwist N f χ hχ2) = fun n => (fun n : ℕ => χ (n : ZMod D)) n * qCoeff f n :=
    funext (qCoeff_normTwist N f χ hχ hχ2)
  rw [hc]
  refine ((isNormalizedEigenform_iff f).mp hf).twist (Dvd.intro _ rfl) _ (by simp)
    (fun m n => by simp) (fun p hp hpM => ?_) (fun p hp hpM hpN => ?_)
  · have hpD : ¬ p ∣ D := fun h => hpM (Dvd.dvd.mul_left (dvd_pow h two_ne_zero) _)
    have hu : IsUnit (p : ZMod D) :=
      (ZMod.isUnit_iff_coprime p D).mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpD)
    simpa [hu.unit_spec] using hχ2 hu.unit
  · have hpD : p ∣ D := hp.dvd_of_dvd_pow ((Nat.Prime.dvd_mul hp).mp hpM |>.resolve_left hpN)
    have hu : ¬ IsUnit (p : ZMod D) := fun h =>
      hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd ((ZMod.isUnit_iff_coprime p D).mp h) hpD)
    exact MulChar.map_nonunit _ hu

end Normalized

/-! ### The twisting property for one `d` -/

/-- Every normalized eigenform has a twist by `(d/·)`. -/
def TwistP (d : ℤ) : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ f : CuspForm (Gamma0 N) 2, f.IsNormalizedEigenform →
    ∃ M : ℕ, 0 < M ∧ N ∣ M ∧ ∃ g : CuspForm (Gamma0 M) 2,
      g.IsNormalizedEigenform ∧ ∀ p : ℕ, (hp : p.Prime) → ¬ p ∣ N → ¬ (p : ℤ) ∣ 2 * d → ¬ p ∣ M →
        qCoeff g p = (@legendreSym p ⟨hp⟩ d : ℂ) * qCoeff f p

lemma twistStatement_iff : TwistStatement ↔ ∀ d : ℤ, d ≠ 0 → TwistP d :=
  ⟨fun h d hd N hN f hf => h N hN f hf d hd, fun h N hN f hf d hd => h d hd N hN f hf⟩

/-- A primitive real character realizing `(d/·)` gives `TwistP d`. -/
theorem twistP_of_char (d : ℤ) {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (hχ : χ.IsPrimitive) (hχ2 : ∀ u : (ZMod D)ˣ, χ u ^ 2 = 1)
    (hval : ∀ p : ℕ, (hp : p.Prime) → ¬ p ∣ D → ¬ (p : ℤ) ∣ 2 * d →
      χ (p : ZMod D) = (@legendreSym p ⟨hp⟩ d : ℂ)) : TwistP d := by
  intro N hN f hf
  have : NeZero N := ⟨hN.ne'⟩
  refine ⟨N * D ^ 2, Nat.mul_pos hN (pow_pos (Nat.pos_of_ne_zero (NeZero.ne D)) 2),
    Dvd.intro _ rfl, normTwist N f χ hχ2, isNormalizedEigenform_normTwist N f hf χ hχ hχ2,
    fun p hp _ hpd hpM => ?_⟩
  have hpD : ¬ p ∣ D := fun h => hpM (Dvd.dvd.mul_left (dvd_pow h two_ne_zero) _)
  rw [qCoeff_normTwist N f χ hχ hχ2, hval p hp hpD hpd]

lemma twistP_one : TwistP 1 := fun N hN f hf =>
  ⟨N, hN, dvd_rfl, f, hf, fun p hp _ _ _ => by
    have := Fact.mk hp
    simp [legendreSym.at_one]⟩

lemma twistP_mul {d₁ d₂ : ℤ} (h₁ : TwistP d₁) (h₂ : TwistP d₂) : TwistP (d₁ * d₂) := by
  intro N hN f hf
  obtain ⟨M₁, hM₁, hNM₁, g₁, hg₁, hc₁⟩ := h₁ N hN f hf
  obtain ⟨M₂, hM₂, hM₁M₂, g₂, hg₂, hc₂⟩ := h₂ M₁ hM₁ g₁ hg₁
  refine ⟨M₂, hM₂, dvd_trans hNM₁ hM₁M₂, g₂, hg₂, fun p hp hpN hpd hpM₂ => ?_⟩
  have := Fact.mk hp
  have hpM₁ : ¬ p ∣ M₁ := fun h => hpM₂ (dvd_trans h hM₁M₂)
  have hd₁ : ¬ (p : ℤ) ∣ 2 * d₁ := fun h => hpd (by
    rw [← mul_assoc]; exact Dvd.dvd.mul_right h _)
  have hd₂ : ¬ (p : ℤ) ∣ 2 * d₂ := fun h => hpd (by
    rw [mul_left_comm]; exact Dvd.dvd.mul_left h _)
  rw [hc₂ p hp hpM₁ hd₂ hpM₂, hc₁ p hp hpN hd₁ hpM₁, legendreSym.mul]
  push_cast
  ring

/-! ### Primitivity -/

section Primitive

variable {D : ℕ} [NeZero D]

/-- A character is primitive if, for every proper divisor `d` of the level, it is nontrivial on
the kernel of `(ZMod D)ˣ → (ZMod d)ˣ`. -/
lemma isPrimitive_of_ker (χ : DirichletCharacter ℂ D)
    (h : ∀ (d : ℕ) (hd : d ∣ D), d ≠ D → ∃ u : (ZMod D)ˣ, ZMod.unitsMap hd u = 1 ∧ χ u ≠ 1) :
    χ.IsPrimitive := by
  by_contra hne
  obtain ⟨u, hu1, hχu⟩ := h _ (DirichletCharacter.conductor_dvd_level χ) hne
  have := (DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := χ)
    (DirichletCharacter.conductor_dvd_level χ)).mp (DirichletCharacter.factorsThrough_conductor χ)
    (MonoidHom.mem_ker.mpr hu1)
  rw [MonoidHom.mem_ker] at this
  exact hχu (by simpa using congrArg Units.val this)

end Primitive

/-- The `ℂ`-valued version of an integer character. -/
abbrev toC {D : ℕ} (χ : MulChar (ZMod D) ℤ) : DirichletCharacter ℂ D :=
  χ.ringHomComp (Int.castRingHom ℂ)

lemma toC_apply {D : ℕ} (χ : MulChar (ZMod D) ℤ) (a : ZMod D) : toC χ a = (χ a : ℂ) := rfl

lemma toC_sq {D : ℕ} (χ : MulChar (ZMod D) ℤ) (hχ : χ.IsQuadratic) (u : (ZMod D)ˣ) :
    toC χ u ^ 2 = 1 := by
  have h := congrArg (fun ψ : MulChar (ZMod D) ℤ => ψ u) hχ.sq_eq_one
  simp only [MulChar.pow_apply_coe, MulChar.one_apply_coe] at h
  rw [toC_apply]
  exact_mod_cast h

lemma unitsMap_eq_one_of_dvd {D d : ℕ} (hd : d ∣ D) (u : (ZMod D)ˣ) (k : ℕ)
    (hu : (u : ZMod D) = (k : ZMod D)) (hk : (k : ZMod d) = 1) : ZMod.unitsMap hd u = 1 := by
  ext
  simp [ZMod.unitsMap_def, hu, hk]

/-! ### The three kinds of generators -/

lemma twistP_neg_one : TwistP (-1) := by
  refine twistP_of_char (-1) (toC ZMod.χ₄) ?_ (toC_sq _ ZMod.isQuadratic_χ₄) ?_
  · refine isPrimitive_of_ker _ fun d hd hne => ?_
    have hd2 : d ∣ 2 := by
      have := Nat.le_of_dvd (by norm_num) hd
      interval_cases d <;> simp_all
    refine ⟨ZMod.unitOfCoprime 3 (by norm_num), unitsMap_eq_one_of_dvd hd _ 3 (by simp) ?_, ?_⟩
    · rw [show (3 : ℕ) = 1 + 2 by rfl, Nat.cast_add, (ZMod.natCast_eq_zero_iff 2 d).mpr hd2]
      simp
    · have h3 : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
      rw [toC_apply, ZMod.coe_unitOfCoprime, Nat.cast_ofNat, h3]
      norm_num
  · intro p hp hp4 hpd
    have := Fact.mk hp
    have hp2 : p ≠ 2 := by rintro rfl; exact hpd (by norm_num)
    rw [toC_apply, legendreSym.at_neg_one hp2]

lemma twistP_two : TwistP 2 := by
  refine twistP_of_char 2 (toC ZMod.χ₈) ?_ (toC_sq _ ZMod.isQuadratic_χ₈) ?_
  · refine isPrimitive_of_ker _ fun d hd hne => ?_
    have hd4 : d ∣ 4 := by
      have := Nat.le_of_dvd (by norm_num) hd
      interval_cases d <;> simp_all
    refine ⟨ZMod.unitOfCoprime 5 (by norm_num), unitsMap_eq_one_of_dvd hd _ 5 (by simp) ?_, ?_⟩
    · rw [show (5 : ℕ) = 1 + 4 by rfl, Nat.cast_add, (ZMod.natCast_eq_zero_iff 4 d).mpr hd4]
      simp
    · have h5 : ZMod.χ₈ (5 : ZMod 8) = -1 := by decide
      rw [toC_apply, ZMod.coe_unitOfCoprime, Nat.cast_ofNat, h5]
      norm_num
  · intro p hp hp8 hpd
    have := Fact.mk hp
    have hp2 : p ≠ 2 := by rintro rfl; exact hpd (by norm_num)
    rw [toC_apply, legendreSym.at_two hp2]

/-- `q* = χ₄(q) q` for an odd prime `q`. -/
lemma twistP_star (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) : TwistP (ZMod.χ₄ q * q) := by
  have := Fact.mk hq
  have : NeZero q := ⟨hq.ne_zero⟩
  have hF : ringChar (ZMod q) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  refine twistP_of_char _ (toC (quadraticChar (ZMod q))) ?_
    (toC_sq _ (quadraticChar_isQuadratic _)) ?_
  · refine isPrimitive_of_ker _ fun d hd hne => ?_
    have hd1 : d = 1 := ((Nat.dvd_prime hq).mp hd).resolve_right hne
    subst hd1
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hF
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    refine ⟨Units.mk0 a ha0, Subsingleton.elim _ _, ?_⟩
    rw [toC_apply, Units.val_mk0, ha]
    norm_num
  · intro p hp hpq hpd
    have := Fact.mk hp
    have hp2 : p ≠ 2 := by rintro rfl; exact hpd (by norm_num)
    have hne : ringChar (ZMod q) ≠ p := by
      rw [ZMod.ringChar_zmod_n]; rintro rfl; exact hpq dvd_rfl
    rw [toC_apply, quadraticChar_odd_prime hF hp2 hne, ZMod.card]
    simp [legendreSym]

lemma twistP_sq_mul {d : ℤ} (k : ℤ) (hk : TwistP k) (hd : TwistP d) : TwistP (k * k * d) :=
  twistP_mul (twistP_mul hk hk) hd

lemma twistP_prime (q : ℕ) (hq : q.Prime) : TwistP q := by
  by_cases hq2 : q = 2
  · subst hq2; exact_mod_cast twistP_two
  · have hodd : q % 2 ≠ 0 := by
      intro h
      rcases hq.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h) with h' | h' <;> omega
    have h4 : ZMod.χ₄ q = 1 ∨ ZMod.χ₄ q = -1 := by
      rw [ZMod.χ₄_nat_eq_if_mod_four]; split_ifs <;> simp_all
    rcases h4 with h4 | h4
    · simpa [h4] using twistP_star q hq hq2
    · simpa [h4] using twistP_mul twistP_neg_one (twistP_star q hq hq2)

theorem twistP_of_ne_zero (d : ℤ) (hd : d ≠ 0) : TwistP d := by
  have hnat : ∀ n : ℕ, n ≠ 0 → TwistP n := by
    intro n
    induction n using induction_on_primes with
    | zero => intro h; exact absurd rfl h
    | one => intro _; exact_mod_cast twistP_one
    | prime_mul p a hp ih =>
      intro hpa
      have ha : a ≠ 0 := fun h => hpa (by simp [h])
      push_cast
      exact twistP_mul (twistP_prime p hp) (ih ha)
  rcases Int.natAbs_eq d with h | h
  · rw [h]; exact hnat _ (Int.natAbs_ne_zero.mpr hd)
  · rw [h, neg_eq_neg_one_mul]
    exact twistP_mul twistP_neg_one (hnat _ (Int.natAbs_ne_zero.mpr hd))

/-- **`TwistStatement` holds.** Twisting normalized eigenforms of weight 2 by quadratic
characters, formalized from Mathlib's Gauss sums and q-expansions. -/
theorem twistStatement : TwistStatement :=
  twistStatement_iff.mpr twistP_of_ne_zero

/-- **Quadratic twists of semistable curves are modular**, assuming only Wiles's theorem for
semistable integral equations (the repo's `modularity_of_semistableModel`). -/
theorem isModular_twist_of_isSemistable' (hWiles : WilesStatement)
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) (d : ℤ) (hd : d ≠ 0) :
    ∃ W₀ : WeierstrassCurve ℤ, W₀.IsIntegralModelOf (W.map (Int.castRingHom ℚ)) ∧
      (twist W₀ d).IsModularModel :=
  isModular_twist_of_isSemistable hWiles twistStatement W hΔ hW d hd

end PilotA
