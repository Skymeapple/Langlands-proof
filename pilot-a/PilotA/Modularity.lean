/-
Pilot A, target H1: Wiles's theorem for every semistable curve over `ℚ`, whatever equation it is
given by.

`WeierstrassCurve.modularity_of_semistableModel` in anthropics/fermats-last-theorem proves
`IsModular` for `W.map ℚ` where `W : WeierstrassCurve ℤ` is a chosen integral equation with
`IsSemistableModel`. Here it is an explicit hypothesis `hWiles` (its exact statement), because the
repo's full build needs ~153 GB of memory. `WithRepo.lean.txt` instantiates it with the repo's
theorem.

The definitions `IsModular`, `IsSemistableModel`, `IsIntegralModelOf` are vendored verbatim from
the repo (`Vendored/Def_FLTPrelim_Modularity.lean`).
-/
import PilotA.SemistableModel
import PilotA.Vendored.Def_FLTPrelim_Modularity

set_option autoImplicit false

namespace PilotA

open WeierstrassCurve

/-- The exact statement of the repo's `WeierstrassCurve.modularity_of_semistableModel`. -/
def WilesStatement : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → W.IsSemistableModel →
    (W.map (Int.castRingHom ℚ)).IsModular

/-- `IsModular` depends only on the curve up to change of variables over `ℚ`. -/
theorem isModular_smul_iff (E : WeierstrassCurve ℚ) (C : VariableChange ℚ) :
    (C • E).IsModular ↔ E.IsModular := by
  constructor
  · rintro ⟨W, ⟨C₁, h₁⟩, hW⟩
    exact ⟨W, ⟨C₁ * C, by rw [mul_smul, h₁]⟩, hW⟩
  · rintro ⟨W, ⟨C₁, h₁⟩, hW⟩
    exact ⟨W, ⟨C₁ * C⁻¹, by rw [mul_smul, inv_smul_smul, h₁]⟩, hW⟩

/-- **Wiles's theorem for intrinsically semistable curves.** Every Weierstrass curve over `ℚ` with
`Δ ≠ 0` that has semistable reduction at every prime (Tate's criterion, on *some* `p`-integral
equation for each `p`) is modular. No integrality or minimality of the given equation is assumed. -/
theorem isModular_of_isSemistable (hWiles : WilesStatement) (E : WeierstrassCurve ℚ)
    (hE : E.Δ ≠ 0) (hss : IsSemistable E) : E.IsModular := by
  obtain ⟨W, C, hC, hΔ, hW⟩ := exists_semistable_model E hE hss
  have := hWiles W hΔ hW
  rw [← hC, isModular_smul_iff] at this
  exact this

/-- The new theorem contains the repo's: a semistable integral equation is intrinsically
semistable. -/
theorem isSemistable_of_isSemistableModel (W : WeierstrassCurve ℤ) (hW : W.IsSemistableModel) :
    IsSemistable (W.map (Int.castRingHom ℚ)) :=
  isSemistable_map W hW

/-- An example outside the repo's theorem: the curve `11a3`, `y² + y = x³ − x²`, written in the
non-minimal equation `y² + 8y = x³ − 4x²` (scaled by `u = 1/2`). Its equation has `2 ∣ Δ` and
`2 ∣ c₄`, so `modularity_of_semistableModel` does not apply to this equation, but the curve is
semistable and the theorem above covers it. -/
def scaled11a3 : WeierstrassCurve ℤ := ⟨0, -4, 8, 0, 0⟩

example : ¬ scaled11a3.IsSemistableModel := by
  intro h
  exact h 2 Nat.prime_two
    (by norm_num [scaled11a3, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])
    (by norm_num [scaled11a3, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄])

def curve11a3 : WeierstrassCurve ℤ := ⟨0, -1, 1, 0, 0⟩

example : curve11a3.IsSemistableModel := by
  intro p hp hΔ
  have hΔ' : curve11a3.Δ = -11 := by norm_num [curve11a3, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  rw [hΔ'] at hΔ
  have hp11 : p = 11 := by
    have : (p : ℤ) ∣ 11 := (dvd_neg).mp hΔ
    have : p ∣ 11 := by exact_mod_cast this
    exact (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp this
  subst hp11
  have hc : curve11a3.c₄ = 16 := by norm_num [curve11a3, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  rw [hc]; norm_num

theorem scaled11a3_isModular (hWiles : WilesStatement) :
    (scaled11a3.map (Int.castRingHom ℚ)).IsModular := by
  let C : VariableChange ℚ := ⟨Units.mk0 2 two_ne_zero, 0, 0, 0⟩
  have hC : C • scaled11a3.map (Int.castRingHom ℚ) = curve11a3.map (Int.castRingHom ℚ) := by
    ext <;> simp [C, scaled11a3, curve11a3, variableChange_a₁, variableChange_a₂,
      variableChange_a₃, variableChange_a₄, variableChange_a₆] <;> norm_num
  rw [← isModular_smul_iff _ C, hC]
  refine hWiles curve11a3 (by rw [show curve11a3.Δ = -11 from by norm_num [curve11a3, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]]; norm_num) ?_
  intro p hp hΔ
  have hΔ' : curve11a3.Δ = -11 := by norm_num [curve11a3, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  rw [hΔ'] at hΔ
  have hp11 : p = 11 := by
    have : (p : ℤ) ∣ 11 := (dvd_neg).mp hΔ
    have : p ∣ 11 := by exact_mod_cast this
    exact (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp this
  subst hp11
  have hc : curve11a3.c₄ = 16 := by norm_num [curve11a3, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  rw [hc]; norm_num

end PilotA
