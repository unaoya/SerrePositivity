module
public import SerrePositivity.DifferentialGraded.Bimodule.UncurryComposition

/-! # uncurryHomの全Hom合成保存の公理監査 -/
@[expose] public section
open SerrePositivity.DifferentialGraded
#print axioms DGFunctor.map_forward_cochain
#print axioms Bimodule.rightCochain_forward
#print axioms Bimodule.leftCochain_forward
#print axioms Bimodule.uncurryHom_forward_pure
#print axioms Bimodule.uncurryHom_comp
