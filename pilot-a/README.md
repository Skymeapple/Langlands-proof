# Pilot A: Wiles's theorem for semistable curves given by any equation

**Status: proved formally** (Lean 4.33.1, Mathlib `db584cd6`), conditional only on the exact statement of
`WeierstrassCurve.modularity_of_semistableModel`, which is a proved theorem of
[anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem) but whose full build
(about 153 GB of memory) could not be run here. All new theorems depend only on
`[propext, Classical.choice, Quot.sound]` (`AxiomCheck.lean`, checked by `#guard_msgs` at build time).

## What is new

The repo proves modularity for `W.map ℚ` where `W : WeierstrassCurve ℤ` is a *chosen integral equation* with
no prime dividing both Δ and c₄ (`IsSemistableModel`). PROOF-PATH.md flags this: "The hypothesis is on a chosen
integral equation." This pilot removes that restriction.

- `PilotA.IsSemistableAt E p`: for some change of variables over ℚ, the equation is p-integral and p does not
  divide both Δ and c₄ (Tate's criterion, Silverman VII.5.1). `PilotA.IsSemistable E`: this holds at every prime.
- `PilotA.exists_semistable_model` (`PilotA/SemistableModel.lean`, Mathlib only): if `E : WeierstrassCurve ℚ`
  has Δ ≠ 0 and is semistable at every prime, then `E` has a global integral model `W` with
  `∀ p prime, p ∣ W.Δ → ¬ p ∣ W.c₄`. This is the existence of a global semistable minimal model over ℚ
  (Silverman VII.1.3(d), VIII.8.2), proved from scratch with `padicNorm`.
- `PilotA.isModular_of_isSemistable` (`PilotA/Modularity.lean`): given `WilesStatement` (the repo theorem's exact
  statement), every such `E` is `IsModular`.
- `PilotA.isSemistable_of_isSemistableModel`: the new hypothesis contains the old one.
- `PilotA.scaled11a3_isModular`: a worked example outside the repo's theorem: `y² + 8y = x³ − 4x²` (curve 11a3
  scaled by u = 1/2), whose equation has 2 ∣ Δ and 2 ∣ c₄.

`PilotA/Vendored/Def_FLTPrelim_Modularity.lean` is the repo's `Definitions/Def_FLTPrelim_Modularity.lean`, byte for
byte. `PilotA/WithRepo.lean.txt` is the instantiation with the repo's theorem, to be compiled inside the repo.

## Proof outline

1. Clear denominators to get an integral model.
2. Strong induction on |Δ| over integral models. If p divides Δ and c₄, compare with the local semistable model
   `C • W`; Tate's criterion forces ‖u‖ₚ = p^(−k) with k ≥ 1.
3. Silverman VII.1.3(d) (`rst_le_one`): r, s, t of the comparison are p-integral (leading-term argument on the
   b₆ relation for p ≠ 2 and the b₈ relation for p = 2).
4. Approximate r, s, t by integers mod p^(3k) and change variables by u = p^k. The new equation is integral at p
   (it differs from the local model by a p-integral change with unit u) and at every other prime, and
   |Δ| drops by p^(12k).

## Build

```sh
cd pilot-a
lake build            # builds PilotA and AxiomCheck; Mathlib is compiled from source if no cache is reachable
```

Imports: only `Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange`, `Mathlib.NumberTheory.Padics.PadicNorm`
and the vendored definitions file's Mathlib imports. See `BLUEPRINT.md` for the map of other narrow hypotheses
and next targets.
