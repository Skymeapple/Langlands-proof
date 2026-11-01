/-
Copyright (c) 2026 Liam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liam
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum

/-!
# Nonvanishing of Gauss sums of primitive Dirichlet characters

The Gauss sum of a primitive Dirichlet character modulo `N`, taken against a primitive additive
character of `ZMod N` with values in a domain in which `N` is invertible, is nonzero.

Mathlib already has `gaussSum_ne_zero_of_nontrivial` over finite fields; the statement here is for
an arbitrary modulus `N`. The proof is Fourier inversion: if `gaussSum χ e = 0`, then by
`gaussSum_mulShift_of_isPrimitive` every twisted sum `∑ a, χ a * e (m * a)` vanishes, and summing
these against `e (-m)` recovers `N * χ 1 = N`.

## Main results

* `DirichletCharacter.gaussSum_ne_zero_of_isPrimitive`
-/

@[expose] public section

namespace DirichletCharacter

variable {R : Type*} [CommRing R] [IsDomain R] {N : ℕ} [NeZero N]

/-- The Gauss sum of a primitive Dirichlet character is nonzero. -/
theorem gaussSum_ne_zero_of_isPrimitive {χ : DirichletCharacter R N} (hχ : χ.IsPrimitive)
    {e : AddChar (ZMod N) R} (he : e.IsPrimitive) (hN : (N : R) ≠ 0) :
    gaussSum χ e ≠ 0 := by
  intro h0
  have hm (m : ZMod N) : ∑ a : ZMod N, χ a * e (m * a) = 0 := by
    have := gaussSum_mulShift_of_isPrimitive e hχ m
    rw [h0, mul_zero] at this
    simpa [gaussSum, AddChar.mulShift_apply] using this
  have hsum : ∑ m : ZMod N, e (-m) * ∑ a : ZMod N, χ a * e (m * a) = 0 := by
    simp [hm]
  have hswap : ∑ m : ZMod N, e (-m) * ∑ a : ZMod N, χ a * e (m * a) =
      ∑ a : ZMod N, χ a * ∑ m : ZMod N, e (m * (a - 1)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun m _ ↦ ?_
    rw [show m * (a - 1) = -m + m * a by ring, AddChar.map_add_eq_mul]
    ring
  rw [hswap] at hsum
  exact hN (by simpa [AddChar.sum_mulShift _ he, sub_eq_zero] using hsum)

/-- The Gauss sum of a primitive complex Dirichlet character against the standard additive
character is nonzero. -/
theorem gaussSum_stdAddChar_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar ≠ 0 :=
  gaussSum_ne_zero_of_isPrimitive hχ (ZMod.isPrimitive_stdAddChar N)
    (Nat.cast_ne_zero.mpr (NeZero.ne N))

end DirichletCharacter
