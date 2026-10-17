module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionCoendCoherence
public import Mathlib.Data.ZMod.Basic

/-! # 相対 tensor の係数変更と単位・結合比較の検査 -/
@[expose] public section
noncomputable section
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory

example (M : RightModule ℤ PUnit) (N : LeftModule ℤ PUnit) :
    IsIso (tensorModuleBaseChangeIso (Int.castRingHom (ZMod 2)) PUnit
      (complexSphere ℤ (-1)) M N).hom := inferInstance

#print axioms yonedaBaseChangeIso
#print axioms ι_yonedaBaseChangeIso
#print axioms yonedaBaseChange_comparison
#print axioms leftYonedaBaseChangeIso
#print axioms ι_leftYonedaBaseChangeIso
#print axioms leftYonedaBaseChange_comparison
#print axioms tensorModuleBaseChangeIso
#print axioms ι_tensorModuleBaseChangeIso
#print axioms tensorModuleBaseChange_comparison

end SerrePositivity.DifferentialGraded.ScalarExtension
