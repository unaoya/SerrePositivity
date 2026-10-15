module
public import SerrePositivity.DifferentialGraded.Bimodule.UncurryRestriction

/-! # uncurryHomの両因子での計算の公理監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded
#print axioms Bimodule.uncurryHom_first
#print axioms Bimodule.uncurryHom_second
