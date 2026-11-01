/-
Pilot A, target H1 (see `pilot-a/BLUEPRINT.md`).

Intrinsic semistability for Weierstrass curves over `ℚ`, and the existence of a global integral
model on which no prime divides both `Δ` and `c₄` (a global semistable minimal model).

References: J. H. Silverman, *The Arithmetic of Elliptic Curves*, VII.1.3(d) (integrality of the
change of variables between integral models), VII.5.1 (Tate's criterion for semistable reduction),
VIII.8.2 (global minimal models over a field of class number one).

Only Mathlib is imported.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.NumberTheory.Padics.PadicNorm

set_option autoImplicit false

namespace PilotA

open WeierstrassCurve

/-! ### Elementary facts about `padicNorm` -/

section Norm

variable {p : ℕ} [hp : Fact p.Prime]

lemma n_add {x y : ℚ} {M : ℚ} (hx : padicNorm p x ≤ M) (hy : padicNorm p y ≤ M) :
    padicNorm p (x + y) ≤ M :=
  le_trans padicNorm.nonarchimedean (max_le hx hy)

lemma n_sub {x y : ℚ} {M : ℚ} (hx : padicNorm p x ≤ M) (hy : padicNorm p y ≤ M) :
    padicNorm p (x - y) ≤ M :=
  le_trans padicNorm.sub (max_le hx hy)

lemma n_neg {x : ℚ} {M : ℚ} (hx : padicNorm p x ≤ M) : padicNorm p (-x) ≤ M := by
  rwa [padicNorm.neg]

lemma n_mul {x y : ℚ} (hx : padicNorm p x ≤ 1) (hy : padicNorm p y ≤ 1) :
    padicNorm p (x * y) ≤ 1 := by
  rw [padicNorm.mul]
  exact mul_le_one₀ hx (padicNorm.nonneg _) hy

lemma n_pow_eq (x : ℚ) (n : ℕ) : padicNorm p (x ^ n) = padicNorm p x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, padicNorm.mul, ih, pow_succ]

lemma n_pow {x : ℚ} (hx : padicNorm p x ≤ 1) (n : ℕ) : padicNorm p (x ^ n) ≤ 1 := by
  rw [n_pow_eq]
  exact pow_le_one₀ (padicNorm.nonneg _) hx

lemma n_int (z : ℤ) : padicNorm p (z : ℚ) ≤ 1 := padicNorm.of_int z

lemma n_ofNat (n : ℕ) [n.AtLeastTwo] : padicNorm p (OfNat.ofNat n : ℚ) ≤ 1 := by
  exact padicNorm.of_nat (p := p) n

lemma n_one : padicNorm p (1 : ℚ) ≤ 1 := by simp

lemma n_zero : padicNorm p (0 : ℚ) ≤ 1 := by simp

/-- Close goals `padicNorm p e ≤ 1` for ring expressions `e` in p-integral atoms. -/
macro "pint" : tactic =>
  `(tactic| repeat' (first
    | with_reducible assumption
    | with_reducible apply n_add
    | with_reducible apply n_sub
    | with_reducible apply n_neg
    | with_reducible apply n_mul
    | with_reducible apply n_pow
    | with_reducible apply n_int
    | with_reducible apply n_ofNat
    | with_reducible apply n_one
    | with_reducible apply n_zero))

/-- A rational number whose `p`-adic norm is at most one has denominator prime to `p`. -/
lemma not_dvd_den {q : ℚ} (hq : padicNorm p q ≤ 1) : ¬ p ∣ q.den := by
  intro hd
  have hnum : ¬ p ∣ q.num.natAbs := by
    intro hn
    have h := Nat.Coprime.coprime_dvd_right hd (Nat.Coprime.coprime_dvd_left hn q.reduced)
    rw [Nat.coprime_self] at h
    exact hp.out.one_lt.ne' h
  have h1 : padicNorm p (q.num : ℚ) = 1 := by
    rw [padicNorm.int_eq_one_iff]
    intro h
    exact hnum (Int.natCast_dvd.mp h)
  have h2 : padicNorm p (q.den : ℚ) < 1 := (padicNorm.nat_lt_one_iff _).mpr hd
  have hqd : q * q.den = q.num := Rat.mul_den_eq_num q
  have := congrArg (padicNorm p) hqd
  rw [padicNorm.mul, h1] at this
  have h0 : 0 ≤ padicNorm p (q.den : ℚ) := padicNorm.nonneg _
  nlinarith [padicNorm.nonneg (p := p) q]

/-- Approximation of a `p`-integral rational by an integer modulo `p ^ M`. -/
lemma exists_int_approx {q : ℚ} (hq : padicNorm p q ≤ 1) (M : ℕ) :
    ∃ z : ℤ, padicNorm p (q - z) ≤ padicNorm p ((p : ℚ) ^ M) := by
  have hd : ¬ p ∣ q.den := not_dvd_den hq
  have hcop : Nat.Coprime (p ^ M) q.den :=
    ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hd).pow_left M
  obtain ⟨a, b, hab⟩ : IsCoprime ((p ^ M : ℕ) : ℤ) (q.den : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hcop
  refine ⟨q.num * b, ?_⟩
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hdn1 : padicNorm p (q.den : ℚ) = 1 := (padicNorm.nat_eq_one_iff _).mpr hd
  have hab' : (a : ℚ) * (p : ℚ) ^ M + (b : ℚ) * q.den = 1 := by exact_mod_cast hab
  have key : q - ((q.num * b : ℤ) : ℚ) = (q.num * a / q.den) * (p : ℚ) ^ M := by
    have gen : ∀ n d P : ℚ, d ≠ 0 → (a : ℚ) * P + (b : ℚ) * d = 1 →
        n / d - n * b = n * a / d * P := by
      intro n d P hd h
      rw [div_sub' hd, div_mul_eq_mul_div, div_left_inj' hd]
      linear_combination -n * h
    have hq' : q = q.num / q.den := (Rat.num_div_den q).symm
    push_cast
    calc q - q.num * b = q.num / q.den - q.num * b := by rw [← hq']
      _ = _ := gen _ _ _ hden hab'
  rw [key, padicNorm.mul, padicNorm.div, padicNorm.mul, hdn1, div_one]
  have h1 := n_int (p := p) q.num
  have h2 := n_int (p := p) a
  have h3 := padicNorm.nonneg (p := p) ((p : ℚ) ^ M)
  have h4 := padicNorm.nonneg (p := p) (q.num : ℚ)
  have h5 := padicNorm.nonneg (p := p) (a : ℚ)
  calc padicNorm p q.num * padicNorm p a * padicNorm p ((p : ℚ) ^ M)
      ≤ 1 * 1 * padicNorm p ((p : ℚ) ^ M) := by gcongr
    _ = _ := by ring

/-- Leading-term lemma: if `a * x ^ (n+1) = y` with `‖a‖ = 1` and `‖y‖ ≤ max 1 ‖x‖ ^ n`,
then `x` is `p`-integral. -/
lemma le_one_of_lead {x a y : ℚ} (n : ℕ) (ha : padicNorm p a = 1) (h : a * x ^ (n + 1) = y)
    (hy : padicNorm p y ≤ max 1 (padicNorm p x ^ n)) : padicNorm p x ≤ 1 := by
  by_contra hx
  push_neg at hx
  have hxn : 1 ≤ padicNorm p x ^ n := one_le_pow₀ hx.le
  rw [max_eq_right hxn, ← h, padicNorm.mul, ha, one_mul, n_pow_eq] at hy
  have : padicNorm p x ^ n < padicNorm p x ^ (n + 1) := pow_lt_pow_right₀ hx (Nat.lt_succ_self n)
  linarith

/-- Terms `b * x ^ j` with `‖b‖ ≤ 1` and `j ≤ n` are bounded by `max 1 ‖x‖ ^ n`. -/
lemma term_le {x b : ℚ} {j n : ℕ} (hb : padicNorm p b ≤ 1) (hj : j ≤ n) :
    padicNorm p (b * x ^ j) ≤ max 1 (padicNorm p x ^ n) := by
  rw [padicNorm.mul, n_pow_eq]
  have h0 := padicNorm.nonneg (p := p) x
  have hxj : padicNorm p x ^ j ≤ max 1 (padicNorm p x ^ n) := by
    rcases le_or_gt (padicNorm p x) 1 with h | h
    · exact le_max_of_le_left (pow_le_one₀ h0 h)
    · exact le_max_of_le_right (pow_le_pow_right₀ h.le hj)
  calc padicNorm p b * padicNorm p x ^ j ≤ 1 * padicNorm p x ^ j := by
        gcongr
    _ ≤ _ := by rw [one_mul]; exact hxj

lemma norm_four_of_ne_two (h2 : p ≠ 2) : padicNorm p (4 : ℚ) = 1 := by
  have : padicNorm p ((4 : ℕ) : ℚ) = 1 := by
    rw [padicNorm.nat_eq_one_iff]
    intro hd
    have : p ∣ 2 := hp.out.dvd_of_dvd_pow (n := 2) (by norm_num at hd ⊢; exact hd)
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  simpa using this

lemma norm_three_of_eq_two (h2 : p = 2) : padicNorm p (3 : ℚ) = 1 := by
  subst h2
  have : padicNorm 2 ((3 : ℕ) : ℚ) = 1 := by
    rw [padicNorm.nat_eq_one_iff]; decide
  simpa using this

end Norm

/-! ### p-integral Weierstrass curves -/

/-- A Weierstrass curve over `ℚ` has `p`-integral coefficients. -/
def IsPIntegral (p : ℕ) (W : WeierstrassCurve ℚ) : Prop :=
  padicNorm p W.a₁ ≤ 1 ∧ padicNorm p W.a₂ ≤ 1 ∧ padicNorm p W.a₃ ≤ 1 ∧
    padicNorm p W.a₄ ≤ 1 ∧ padicNorm p W.a₆ ≤ 1

/-- `E` is *semistable at `p`* (Tate's criterion, Silverman VII.5.1): some change of variables over
`ℚ` gives a `p`-integral equation on which `p` does not divide both `Δ` and `c₄`. This is a property
of the curve `E` up to isomorphism over `ℚ`, not of a chosen equation. -/
def IsSemistableAt (E : WeierstrassCurve ℚ) (p : ℕ) : Prop :=
  ∃ C : VariableChange ℚ, IsPIntegral p (C • E) ∧
    (padicNorm p (C • E).Δ = 1 ∨ padicNorm p (C • E).c₄ = 1)

/-- `E` is semistable: semistable at every prime. -/
def IsSemistable (E : WeierstrassCurve ℚ) : Prop :=
  ∀ p : ℕ, p.Prime → IsSemistableAt E p

section PIntegral

variable {p : ℕ} [hp : Fact p.Prime]

lemma IsPIntegral.b₂ {W : WeierstrassCurve ℚ} (h : IsPIntegral p W) : padicNorm p W.b₂ ≤ 1 := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := h; simp only [WeierstrassCurve.b₂]; pint

lemma IsPIntegral.b₄ {W : WeierstrassCurve ℚ} (h : IsPIntegral p W) : padicNorm p W.b₄ ≤ 1 := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := h; simp only [WeierstrassCurve.b₄]; pint

lemma IsPIntegral.b₆ {W : WeierstrassCurve ℚ} (h : IsPIntegral p W) : padicNorm p W.b₆ ≤ 1 := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := h; simp only [WeierstrassCurve.b₆]; pint

lemma IsPIntegral.b₈ {W : WeierstrassCurve ℚ} (h : IsPIntegral p W) : padicNorm p W.b₈ ≤ 1 := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := h; simp only [WeierstrassCurve.b₈]; pint

lemma isPIntegral_map_int (W : WeierstrassCurve ℤ) : IsPIntegral p (W.map (Int.castRingHom ℚ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
    eq_intCast] <;> exact n_int _

/-- A change of variables with `p`-integral `u⁻¹, r, s, t` preserves `p`-integrality. -/
lemma IsPIntegral.smul {W : WeierstrassCurve ℚ} (hW : IsPIntegral p W) (C : VariableChange ℚ)
    (hu : padicNorm p ((C.u⁻¹ : ℚˣ) : ℚ) ≤ 1) (hr : padicNorm p C.r ≤ 1)
    (hs : padicNorm p C.s ≤ 1) (ht : padicNorm p C.t ≤ 1) : IsPIntegral p (C • W) := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [variableChange_a₁]; pint
  · rw [variableChange_a₂]; pint
  · rw [variableChange_a₃]; pint
  · rw [variableChange_a₄]; pint
  · rw [variableChange_a₆]; pint

lemma unit_pow_mul_inv_pow (u : ℚˣ) (n : ℕ) : (u : ℚ) ^ n * ((u⁻¹ : ℚˣ) : ℚ) ^ n = 1 := by
  rw [← mul_pow, Units.mul_inv, one_pow]

/-- Silverman VII.1.3(d): if `W` and `C • W` are both `p`-integral and `u` is `p`-integral, then
`r`, `s`, `t` are `p`-integral. -/
theorem rst_le_one {W : WeierstrassCurve ℚ} (hW : IsPIntegral p W) (C : VariableChange ℚ)
    (hC : IsPIntegral p (C • W)) (hu : padicNorm p (C.u : ℚ) ≤ 1) :
    padicNorm p C.r ≤ 1 ∧ padicNorm p C.s ≤ 1 ∧ padicNorm p C.t ≤ 1 := by
  set u : ℚ := (C.u : ℚ) with hu_def
  have hinv := unit_pow_mul_inv_pow C.u
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  obtain ⟨h1', h2', h3', h4', h6'⟩ := hC
  have hb2 := IsPIntegral.b₂ ⟨h1, h2, h3, h4, h6⟩
  have hb4 := IsPIntegral.b₄ ⟨h1, h2, h3, h4, h6⟩
  have hb6 := IsPIntegral.b₆ ⟨h1, h2, h3, h4, h6⟩
  have hb8 := IsPIntegral.b₈ ⟨h1, h2, h3, h4, h6⟩
  have hb6' := IsPIntegral.b₆ ⟨h1', h2', h3', h4', h6'⟩
  have hb8' := IsPIntegral.b₈ ⟨h1', h2', h3', h4', h6'⟩
  -- `r`
  have hr : padicNorm p C.r ≤ 1 := by
    by_cases h2p : p = 2
    · have e : u ^ 8 * (C • W).b₈ =
          W.b₈ + 3 * C.r * W.b₆ + 3 * C.r ^ 2 * W.b₄ + C.r ^ 3 * W.b₂ + 3 * C.r ^ 4 := by
        rw [variableChange_b₈, ← mul_assoc, hinv 8, one_mul]
      refine le_one_of_lead 3 (norm_three_of_eq_two h2p)
        (y := u ^ 8 * (C • W).b₈ - W.b₈ - (3 * W.b₆) * C.r ^ 1 - (3 * W.b₄) * C.r ^ 2
          - W.b₂ * C.r ^ 3) (by linear_combination -e) ?_
      refine n_sub (n_sub (n_sub (n_sub ?_ ?_) ?_) ?_) ?_
      · exact le_trans (by pint) (le_max_left _ _)
      · exact le_trans (by pint) (le_max_left _ _)
      · exact term_le (by pint) (by norm_num)
      · exact term_le (by pint) (by norm_num)
      · exact term_le (by pint) (by norm_num)
    · have e : u ^ 6 * (C • W).b₆ = W.b₆ + 2 * C.r * W.b₄ + C.r ^ 2 * W.b₂ + 4 * C.r ^ 3 := by
        rw [variableChange_b₆, ← mul_assoc, hinv 6, one_mul]
      refine le_one_of_lead 2 (norm_four_of_ne_two h2p)
        (y := u ^ 6 * (C • W).b₆ - W.b₆ - (2 * W.b₄) * C.r ^ 1 - W.b₂ * C.r ^ 2)
        (by linear_combination -e) ?_
      refine n_sub (n_sub (n_sub ?_ ?_) ?_) ?_
      · exact le_trans (by pint) (le_max_left _ _)
      · exact le_trans (by pint) (le_max_left _ _)
      · exact term_le (by pint) (by norm_num)
      · exact term_le (by pint) (by norm_num)
  -- `s`
  have hs : padicNorm p C.s ≤ 1 := by
    have e : u ^ 2 * (C • W).a₂ = W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2 := by
      rw [variableChange_a₂, ← mul_assoc, hinv 2, one_mul]
    refine le_one_of_lead 1 (padicNorm.one (p := p))
      (y := W.a₂ + 3 * C.r - u ^ 2 * (C • W).a₂ - W.a₁ * C.s ^ 1) (by linear_combination e) ?_
    refine n_sub (n_sub (n_add ?_ ?_) ?_) ?_
    · exact le_trans (by pint) (le_max_left _ _)
    · exact le_trans (by pint) (le_max_left _ _)
    · exact le_trans (by pint) (le_max_left _ _)
    · exact term_le (by pint) (by norm_num)
  -- `t`
  have ht : padicNorm p C.t ≤ 1 := by
    have e : u ^ 6 * (C • W).a₆ = W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - C.t * W.a₃
        - C.t ^ 2 - C.r * C.t * W.a₁ := by
      rw [variableChange_a₆, ← mul_assoc, hinv 6, one_mul]
    refine le_one_of_lead 1 (padicNorm.one (p := p))
      (y := W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 - u ^ 6 * (C • W).a₆
        - (W.a₃ + C.r * W.a₁) * C.t ^ 1) (by linear_combination e) ?_
    refine n_sub (n_sub ?_ ?_) ?_
    · exact le_trans (by pint) (le_max_left _ _)
    · exact le_trans (by pint) (le_max_left _ _)
    · exact term_le (by pint) (by norm_num)
  exact ⟨hr, hs, ht⟩

end PIntegral

/-! ### From `p`-integral at every prime to integral -/

lemma exists_int_of_forall_le_one {q : ℚ} (h : ∀ ℓ : ℕ, ℓ.Prime → padicNorm ℓ q ≤ 1) :
    ∃ z : ℤ, q = z := by
  refine ⟨q.num, ?_⟩
  have hden : q.den = 1 := by
    by_contra hne
    obtain ⟨ℓ, hℓ, hdvd⟩ := Nat.exists_prime_and_dvd hne
    haveI := Fact.mk hℓ
    exact not_dvd_den (h ℓ hℓ) hdvd
  exact (Rat.coe_int_num_of_den_eq_one hden).symm

lemma exists_int_model {W : WeierstrassCurve ℚ} (h : ∀ ℓ : ℕ, (hℓ : ℓ.Prime) →
    IsPIntegral ℓ W) : ∃ W' : WeierstrassCurve ℤ, W'.map (Int.castRingHom ℚ) = W := by
  obtain ⟨z1, e1⟩ := exists_int_of_forall_le_one (fun ℓ hℓ => (h ℓ hℓ).1)
  obtain ⟨z2, e2⟩ := exists_int_of_forall_le_one (fun ℓ hℓ => (h ℓ hℓ).2.1)
  obtain ⟨z3, e3⟩ := exists_int_of_forall_le_one (fun ℓ hℓ => (h ℓ hℓ).2.2.1)
  obtain ⟨z4, e4⟩ := exists_int_of_forall_le_one (fun ℓ hℓ => (h ℓ hℓ).2.2.2.1)
  obtain ⟨z6, e6⟩ := exists_int_of_forall_le_one (fun ℓ hℓ => (h ℓ hℓ).2.2.2.2)
  refine ⟨⟨z1, z2, z3, z4, z6⟩, ?_⟩
  ext <;> simp [e1, e2, e3, e4, e6]

/-- Every Weierstrass curve over `ℚ` has an integral model. -/
lemma exists_integral_model (E : WeierstrassCurve ℚ) :
    ∃ (W : WeierstrassCurve ℤ) (C : VariableChange ℚ), C • E = W.map (Int.castRingHom ℚ) := by
  set d : ℚ := ((E.a₁.den * E.a₂.den * E.a₃.den * E.a₄.den * E.a₆.den : ℕ) : ℚ) with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; norm_cast
    simp only [mul_ne_zero_iff]; exact ⟨⟨⟨⟨E.a₁.den_nz, E.a₂.den_nz⟩, E.a₃.den_nz⟩,
      E.a₄.den_nz⟩, E.a₆.den_nz⟩
  let C : VariableChange ℚ := ⟨(Units.mk0 d hd0)⁻¹, 0, 0, 0⟩
  have hCu : ((C.u⁻¹ : ℚˣ) : ℚ) = d := by simp [C]
  -- `d * aᵢ` is an integer
  have hint : ∀ (q : ℚ) (m : ℕ), d = (q.den * m : ℕ) → ∀ ℓ : ℕ, ℓ.Prime →
      padicNorm ℓ (d * q) ≤ 1 := by
    intro q m hdm ℓ hℓ
    haveI := Fact.mk hℓ
    have : d * q = q.num * (m : ℤ) := by
      rw [hdm]; push_cast
      rw [mul_comm (q.den : ℚ), mul_assoc, mul_comm (q.den : ℚ), Rat.mul_den_eq_num, mul_comm]
    rw [this]; exact n_mul (n_int _) (by exact_mod_cast n_int (p := ℓ) (m : ℤ))
  have hdl : ∀ ℓ : ℕ, ℓ.Prime → padicNorm ℓ d ≤ 1 := fun ℓ hℓ => by
    haveI := Fact.mk hℓ; rw [hd]; exact padicNorm.of_nat _
  have k1 := hint E.a₁ (E.a₂.den * E.a₃.den * E.a₄.den * E.a₆.den) (by rw [hd]; push_cast; ring)
  have k2 := hint E.a₂ (E.a₁.den * E.a₃.den * E.a₄.den * E.a₆.den) (by rw [hd]; push_cast; ring)
  have k3 := hint E.a₃ (E.a₁.den * E.a₂.den * E.a₄.den * E.a₆.den) (by rw [hd]; push_cast; ring)
  have k4 := hint E.a₄ (E.a₁.den * E.a₂.den * E.a₃.den * E.a₆.den) (by rw [hd]; push_cast; ring)
  have k6 := hint E.a₆ (E.a₁.den * E.a₂.den * E.a₃.den * E.a₄.den) (by rw [hd]; push_cast; ring)
  obtain ⟨W, hW⟩ := exists_int_model (W := C • E) (fun ℓ hℓ => by
    haveI := Fact.mk hℓ
    have hdl := hdl ℓ hℓ
    have k1 := k1 ℓ hℓ; have k2 := k2 ℓ hℓ; have k3 := k3 ℓ hℓ; have k4 := k4 ℓ hℓ
    have k6 := k6 ℓ hℓ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [variableChange_a₁, hCu]; simpa [C] using k1
    · rw [variableChange_a₂, hCu]
      have : d ^ 2 * (E.a₂ - C.s * E.a₁ + 3 * C.r - C.s ^ 2) = d * (d * E.a₂) := by simp [C]; ring
      rw [this]; pint
    · rw [variableChange_a₃, hCu]
      have : d ^ 3 * (E.a₃ + C.r * E.a₁ + 2 * C.t) = d ^ 2 * (d * E.a₃) := by simp [C]; ring
      rw [this]; pint
    · rw [variableChange_a₄, hCu]
      have : d ^ 4 * (E.a₄ - C.s * E.a₃ + 2 * C.r * E.a₂ - (C.t + C.r * C.s) * E.a₁ + 3 * C.r ^ 2
          - 2 * C.s * C.t) = d ^ 3 * (d * E.a₄) := by simp [C]; ring
      rw [this]; pint
    · rw [variableChange_a₆, hCu]
      have : d ^ 6 * (E.a₆ + C.r * E.a₄ + C.r ^ 2 * E.a₂ + C.r ^ 3 - C.t * E.a₃ - C.t ^ 2
          - C.r * C.t * E.a₁) = d ^ 5 * (d * E.a₆) := by simp [C]; ring
      rw [this]; pint)
  exact ⟨W, C, hW.symm⟩

/-! ### The descent step -/

/-- If an integral model `W` of a curve `E` that is semistable at `p` has `p ∣ Δ` and `p ∣ c₄`,
then `E` has an integral model with strictly smaller `|Δ|`. -/
theorem exists_smaller_model (E : WeierstrassCurve ℚ) (W : WeierstrassCurve ℤ)
    (C₀ : VariableChange ℚ) (h₀ : C₀ • E = W.map (Int.castRingHom ℚ)) (hΔ : W.Δ ≠ 0)
    (p : ℕ) [hp : Fact p.Prime] (hpΔ : (p : ℤ) ∣ W.Δ) (hpc : (p : ℤ) ∣ W.c₄)
    (hloc : IsSemistableAt E p) :
    ∃ (W' : WeierstrassCurve ℤ) (C' : VariableChange ℚ),
      C' • E = W'.map (Int.castRingHom ℚ) ∧ W'.Δ ≠ 0 ∧ W'.Δ.natAbs < W.Δ.natAbs := by
  obtain ⟨Cp, hpint, hss⟩ := hloc
  set Wq := W.map (Int.castRingHom ℚ) with hWq
  set C : VariableChange ℚ := Cp * C₀⁻¹ with hC
  have hCW : C • Wq = Cp • E := by
    rw [hC, mul_smul, ← h₀, inv_smul_smul]
  set u : ℚ := (C.u : ℚ) with hu_def
  have hu0 : u ≠ 0 := C.u.ne_zero
  have hinv := unit_pow_mul_inv_pow C.u
  -- norms of `Δ` and `c₄` of `W`
  have hΔq : padicNorm p Wq.Δ < 1 := by
    rw [hWq, map_Δ, eq_intCast]; exact (padicNorm.int_lt_one_iff _).mpr hpΔ
  have hc4q : padicNorm p Wq.c₄ < 1 := by
    rw [hWq, map_c₄, eq_intCast]; exact (padicNorm.int_lt_one_iff _).mpr hpc
  have eΔ : Wq.Δ = u ^ 12 * (C • Wq).Δ := by
    rw [variableChange_Δ, ← mul_assoc, hinv 12, one_mul]
  have ec4 : Wq.c₄ = u ^ 4 * (C • Wq).c₄ := by
    rw [variableChange_c₄, ← mul_assoc, hinv 4, one_mul]
  have hu1 : padicNorm p u < 1 := by
    rcases hss with h | h
    · rw [← hCW] at h
      rw [eΔ, padicNorm.mul, h, mul_one, n_pow_eq] at hΔq
      exact (pow_lt_one_iff_of_nonneg (padicNorm.nonneg _) (by norm_num)).mp hΔq
    · rw [← hCW] at h
      rw [ec4, padicNorm.mul, h, mul_one, n_pow_eq] at hc4q
      exact (pow_lt_one_iff_of_nonneg (padicNorm.nonneg _) (by norm_num)).mp hc4q
  -- the exponent `k = v_p(u) ≥ 1`
  set k : ℤ := padicValRat p u with hk
  have hnu : padicNorm p u = (p : ℚ) ^ (-k) := padicNorm.eq_zpow_of_nonzero hu0
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  have hkpos : 0 < k := by
    rw [hnu] at hu1
    by_contra hk0; push_neg at hk0
    have : (1 : ℚ) ≤ (p : ℚ) ^ (-k) := one_le_zpow₀ hp1.le (by omega)
    linarith
  set kn : ℕ := k.toNat with hkn
  have hkn' : (kn : ℤ) = k := Int.toNat_of_nonneg hkpos.le
  have hkn1 : 1 ≤ kn := by omega
  set π : ℚ := (p : ℚ) ^ kn with hπ
  have hπ0 : π ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hpnorm : padicNorm p (p : ℚ) = (p : ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime
  have hnπ : padicNorm p π = padicNorm p u := by
    rw [hπ, n_pow_eq, hpnorm, hnu, ← hkn', inv_pow, zpow_neg, zpow_natCast]
  obtain ⟨a, ha⟩ : ∃ a : ℚ, a = padicNorm p π := ⟨_, rfl⟩
  have ha0 : 0 < a := by
    rw [ha]; exact lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.nonzero hπ0))
  have ha1 : a ≤ 1 := by rw [ha, hnπ]; exact hu1.le
  have ninv : ∀ x : ℚ, padicNorm p x⁻¹ = (padicNorm p x)⁻¹ := fun x => by
    rw [inv_eq_one_div, padicNorm.div, padicNorm.one, one_div]
  have hua : padicNorm p u = a := by rw [ha, hnπ]
  have hnuinv : padicNorm p u⁻¹ = a⁻¹ := by rw [ninv, hua]
  -- `r, s, t` are `p`-integral
  obtain ⟨hr, hs, ht⟩ := rst_le_one (isPIntegral_map_int W) C (by rw [hCW]; exact hpint) hu1.le
  have hpM : padicNorm p ((p : ℚ) ^ (kn * 3)) = a ^ 3 := by
    rw [pow_mul, ← hπ, n_pow_eq, ← ha]
  obtain ⟨R, hR⟩ := exists_int_approx hr (kn * 3)
  obtain ⟨S, hS⟩ := exists_int_approx hs (kn * 3)
  obtain ⟨T, hT⟩ := exists_int_approx ht (kn * 3)
  rw [hpM] at hR hS hT
  have hR' : padicNorm p ((R : ℚ) - C.r) ≤ a ^ 3 := by rwa [← neg_sub, padicNorm.neg]
  have hS' : padicNorm p ((S : ℚ) - C.s) ≤ a ^ 3 := by rwa [← neg_sub, padicNorm.neg]
  have hT' : padicNorm p ((T : ℚ) - C.t) ≤ a ^ 3 := by rwa [← neg_sub, padicNorm.neg]
  -- the global change of variables
  let C' : VariableChange ℚ := ⟨Units.mk0 π hπ0, R, S, T⟩
  -- the comparison change `D` with `D * C = C'`
  let D : VariableChange ℚ := ⟨Units.mk0 π hπ0 * C.u⁻¹, (R - C.r) * u⁻¹ ^ 2, (S - C.s) * u⁻¹,
    (T - C.t - (R - C.r) * u⁻¹ ^ 2 * C.s * u ^ 2) * u⁻¹ ^ 3⟩
  have hDC : D * C = C' := by
    rw [VariableChange.mul_def]
    congr 1
    · ext; simp [D, C', hu_def]
    · simp only [D, C']; field_simp; ring
    · simp only [D, C']; field_simp; ring
    · simp only [D, C']; field_simp; ring
  have hDp : IsPIntegral p (D • (C • Wq)) := by
    rw [hCW]
    refine hpint.smul D ?_ ?_ ?_ ?_
    · have : ((D.u⁻¹ : ℚˣ) : ℚ) = (π * u⁻¹)⁻¹ := by simp [D, hu_def]
      rw [this, ninv, padicNorm.mul, hnuinv, ← ha]
      field_simp; rfl
    · show padicNorm p ((R - C.r) * u⁻¹ ^ 2) ≤ 1
      rw [padicNorm.mul, n_pow_eq, hnuinv]
      calc padicNorm p ((R : ℚ) - C.r) * a⁻¹ ^ 2 ≤ a ^ 3 * a⁻¹ ^ 2 := by gcongr
        _ = a := by field_simp
        _ ≤ 1 := ha1
    · show padicNorm p ((S - C.s) * u⁻¹) ≤ 1
      rw [padicNorm.mul, hnuinv]
      calc padicNorm p ((S : ℚ) - C.s) * a⁻¹ ≤ a ^ 3 * a⁻¹ := by gcongr
        _ = a ^ 2 := by field_simp
        _ ≤ 1 := pow_le_one₀ ha0.le ha1
    · show padicNorm p ((T - C.t - (R - C.r) * u⁻¹ ^ 2 * C.s * u ^ 2) * u⁻¹ ^ 3) ≤ 1
      have e1 : (R - C.r) * u⁻¹ ^ 2 * C.s * u ^ 2 = (R - C.r) * C.s := by field_simp
      rw [e1, padicNorm.mul, n_pow_eq, hnuinv]
      have hb : padicNorm p ((T : ℚ) - C.t - (R - C.r) * C.s) ≤ a ^ 3 := by
        refine n_sub hT' ?_
        rw [padicNorm.mul]
        calc padicNorm p ((R : ℚ) - C.r) * padicNorm p C.s ≤ a ^ 3 * 1 := by
              gcongr
              exact padicNorm.nonneg _
          _ = a ^ 3 := mul_one _
      calc padicNorm p ((T : ℚ) - C.t - (R - C.r) * C.s) * a⁻¹ ^ 3 ≤ a ^ 3 * a⁻¹ ^ 3 := by
            gcongr
        _ = 1 := by field_simp
        _ ≤ 1 := le_rfl
  have hC'W : C' • Wq = D • (C • Wq) := by rw [← mul_smul, hDC]
  have hall : ∀ ℓ : ℕ, ℓ.Prime → IsPIntegral ℓ (C' • Wq) := by
    intro ℓ hℓ
    rcases eq_or_ne ℓ p with rfl | hne
    · rw [hC'W]; exact hDp
    · haveI := Fact.mk hℓ
      refine (isPIntegral_map_int W).smul C' ?_ (n_int R) (n_int S) (n_int T)
      have hpℓ : padicNorm ℓ (p : ℚ) = 1 := by
        rw [padicNorm.nat_eq_one_iff]
        intro hd
        exact hne ((Nat.prime_dvd_prime_iff_eq hℓ hp.out).mp hd)
      have : ((C'.u⁻¹ : ℚˣ) : ℚ) = π⁻¹ := by simp [C']
      rw [this, inv_eq_one_div, padicNorm.div, padicNorm.one, hπ, n_pow_eq, hpℓ]
      simp
  obtain ⟨W', hW'⟩ := exists_int_model hall
  have eΔ' : (W.Δ : ℚ) = ((p ^ (kn * 12) * W'.Δ : ℤ) : ℚ) := by
    have e1 : ((W'.Δ : ℤ) : ℚ) = π⁻¹ ^ 12 * (W.Δ : ℚ) := by
      have := congrArg WeierstrassCurve.Δ hW'
      rw [map_Δ, eq_intCast] at this
      rw [this, variableChange_Δ, hWq, map_Δ, eq_intCast]
      simp [C']
    push_cast
    rw [e1, pow_mul, ← hπ]
    field_simp
  have eΔ : W.Δ = p ^ (kn * 12) * W'.Δ := by exact_mod_cast eΔ'
  have hΔ' : W'.Δ ≠ 0 := by
    intro h; rw [h, mul_zero] at eΔ; exact hΔ eΔ
  refine ⟨W', C' * C₀, ?_, hΔ', ?_⟩
  · rw [mul_smul, h₀, hW']
  · rw [eΔ, Int.natAbs_mul, Int.natAbs_pow]
    have h1 : 1 < (p : ℤ).natAbs ^ (kn * 12) := by
      rw [Int.natAbs_natCast]
      exact Nat.one_lt_pow (by omega) hp.out.one_lt
    have h2 : 0 < W'.Δ.natAbs := Int.natAbs_pos.mpr hΔ'
    exact (Nat.lt_mul_iff_one_lt_left h2).mpr h1

/-! ### Global semistable models -/

/-- **Existence of a global semistable model.** A Weierstrass curve over `ℚ` with `Δ ≠ 0` that is
semistable at every prime (in the intrinsic sense of `IsSemistableAt`) has an integral model on
which no prime divides both `Δ` and `c₄`. -/
theorem exists_semistable_model (E : WeierstrassCurve ℚ) (hE : E.Δ ≠ 0) (hss : IsSemistable E) :
    ∃ (W : WeierstrassCurve ℤ) (C : VariableChange ℚ), C • E = W.map (Int.castRingHom ℚ) ∧
      W.Δ ≠ 0 ∧ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ W.Δ → ¬ (p : ℤ) ∣ W.c₄ := by
  suffices key : ∀ n : ℕ, ∀ (W : WeierstrassCurve ℤ) (C : VariableChange ℚ),
      C • E = W.map (Int.castRingHom ℚ) → W.Δ ≠ 0 → W.Δ.natAbs = n →
      ∃ (W : WeierstrassCurve ℤ) (C : VariableChange ℚ), C • E = W.map (Int.castRingHom ℚ) ∧
        W.Δ ≠ 0 ∧ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ W.Δ → ¬ (p : ℤ) ∣ W.c₄ by
    obtain ⟨W, C, h⟩ := exists_integral_model E
    have hΔ : W.Δ ≠ 0 := by
      intro h0
      have := congrArg WeierstrassCurve.Δ h
      rw [map_Δ, h0, map_zero, variableChange_Δ] at this
      exact hE ((mul_eq_zero.mp this).resolve_left (pow_ne_zero _ (Units.ne_zero _)))
    exact key _ W C h hΔ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W C h hΔ hn
    by_cases hs : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ W.Δ → ¬ (p : ℤ) ∣ W.c₄
    · exact ⟨W, C, h, hΔ, hs⟩
    · push_neg at hs
      obtain ⟨p, hp, h1, h2⟩ := hs
      haveI := Fact.mk hp
      obtain ⟨W', C', h', hΔ', hlt⟩ := exists_smaller_model E W C h hΔ p h1 h2 (hss p hp)
      exact ih _ (hn ▸ hlt) W' C' h' hΔ' rfl

/-- Conversely, a semistable integral model gives a curve that is semistable in the intrinsic
sense, so `IsSemistable` really generalises the repo's `IsSemistableModel`. -/
theorem isSemistable_map (W : WeierstrassCurve ℤ)
    (hss : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ W.Δ → ¬ (p : ℤ) ∣ W.c₄) :
    IsSemistable (W.map (Int.castRingHom ℚ)) := by
  intro p hp
  haveI := Fact.mk hp
  refine ⟨1, by rw [one_smul]; exact isPIntegral_map_int W, ?_⟩
  rw [one_smul, map_Δ, map_c₄, eq_intCast, eq_intCast]
  by_cases h : (p : ℤ) ∣ W.Δ
  · exact Or.inr ((padicNorm.int_eq_one_iff _).mpr (hss p hp h))
  · exact Or.inl ((padicNorm.int_eq_one_iff _).mpr h)

end PilotA
