/-
Pilot A, milestone 3, step 5 (see `BLUEPRINT.md` §4): the eigenform axioms of
`CuspForm.IsNormalizedEigenform` are preserved when the coefficients are twisted by a completely
multiplicative `χ` with `χ(p)² = 1` away from the new level and `χ(p) = 0` at the new primes.
Pure algebra on coefficient sequences.
-/
import PilotA.Vendored.Def_FLTPrelim_Modularity

set_option autoImplicit false

namespace PilotA

/-- The coefficient conditions of `CuspForm.IsNormalizedEigenform` at level `N`. -/
structure IsEigenCoeffs (N : ℕ) (a : ℕ → ℂ) : Prop where
  one : a 1 = 1
  mul_of_coprime : ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n
  prime_pow_of_not_dvd : ∀ p r : ℕ, p.Prime → ¬ p ∣ N →
    a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - p * a (p ^ r)
  prime_pow_of_dvd : ∀ p r : ℕ, p.Prime → p ∣ N → a (p ^ (r + 2)) = a p * a (p ^ (r + 1))

theorem isNormalizedEigenform_iff {N : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    f.IsNormalizedEigenform ↔ IsEigenCoeffs N (ModularFormClass.qCoeff f) :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩

lemma map_pow_of_mul {χ : ℕ → ℂ} (hχ1 : χ 1 = 1) (hχ : ∀ m n, χ (m * n) = χ m * χ n)
    (p r : ℕ) : χ (p ^ r) = χ p ^ r := by
  induction r with
  | zero => simp [hχ1]
  | succ r ih => rw [pow_succ, hχ, ih, pow_succ]

/-- **Twisting preserves the eigenform coefficient axioms.** -/
theorem IsEigenCoeffs.twist {N M : ℕ} {a : ℕ → ℂ} (ha : IsEigenCoeffs N a) (hNM : N ∣ M)
    (χ : ℕ → ℂ) (hχ1 : χ 1 = 1) (hχ : ∀ m n, χ (m * n) = χ m * χ n)
    (hχsq : ∀ p : ℕ, p.Prime → ¬ p ∣ M → χ p ^ 2 = 1)
    (hχ0 : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ N → χ p = 0) :
    IsEigenCoeffs M (fun n => χ n * a n) := by
  have hpow := map_pow_of_mul hχ1 hχ
  refine ⟨by simp [hχ1, ha.one], fun m n hmn => ?_, fun p r hp hpM => ?_, fun p r hp hpM => ?_⟩
  · simp only [hχ, ha.mul_of_coprime m n hmn]; ring
  · have hpN : ¬ p ∣ N := fun h => hpM (dvd_trans h hNM)
    simp only [hpow, ha.prime_pow_of_not_dvd p r hp hpN]
    have h2 := hχsq p hp hpM
    linear_combination (-(p : ℂ) * a (p ^ r) * χ p ^ r) * h2
  · by_cases hpN : p ∣ N
    · simp only [hpow, ha.prime_pow_of_dvd p r hp hpN, pow_one]; ring
    · simp only [hpow, hχ0 p hp hpM hpN, pow_one]
      simp
