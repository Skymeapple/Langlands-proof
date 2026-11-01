import PilotD.GaussSum
import PilotD.TwistQExpansion
import PilotD.Newforms

/-! Every main result of Pilot D uses only the standard axioms. -/

set_option linter.style.whitespace false

/-- info: 'DirichletCharacter.gaussSum_ne_zero_of_isPrimitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms DirichletCharacter.gaussSum_ne_zero_of_isPrimitive

/-- info: 'ModularForm.twistSum_slash_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ModularForm.twistSum_slash_eq

/-- info: 'CuspForm.twistSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CuspForm.twistSum

/-- info: 'CuspForm.qExpansion_coeff_twist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CuspForm.qExpansion_coeff_twist

/-- info: 'CongruenceSubgroup.conj_frickeMatrix_Gamma0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CongruenceSubgroup.conj_frickeMatrix_Gamma0

/-- info: 'ModularForm.fricke_fricke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ModularForm.fricke_fricke

/-- info: 'CuspForm.fricke_fricke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CuspForm.fricke_fricke

/-- info: 'ModularForm.fricke_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ModularForm.fricke_apply

/-- info: 'CuspForm.levelRaise_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CuspForm.levelRaise_apply

/-- info: 'CuspForm.levelRaise_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CuspForm.levelRaise_injective

/-- info: 'CuspForm.traceₗ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CuspForm.traceₗ

/-- info: 'CuspForm.NewformDecomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CuspForm.NewformDecomposition

/-- info: 'CuspForm.newformDecomposition_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CuspForm.newformDecomposition_one
