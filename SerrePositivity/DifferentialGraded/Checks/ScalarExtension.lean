module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.CategoriesAndModules
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # 非 flat な係数変更の型検査と公理監査 -/
@[expose] public section
noncomputable section
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory

-- ℤ → ℤ/2 に平坦性の instance を要求せず適用できる。
example : (extension (Int.castRingHom (ZMod 2))).Monoidal := inferInstance

example : DGCategory (ZMod 2)
    (DGBaseChange (Int.castRingHom (ZMod 2)) (Complex ℤ)) := inferInstance

#print axioms adjunction
#print axioms coproductIso
#print axioms map_ι_coproductIso
#print axioms coequalizerIso
#print axioms map_π_coequalizerIso
#print axioms tensorIso_naturality
#print axioms identityIso
#print axioms compositionIso
#print axioms sphereIso
#print axioms tensorIso_left_unitor
#print axioms tensorIso_right_unitor
#print axioms tensorIso_associator
#print axioms extensionMonoidal
#print axioms dgFunctor

end SerrePositivity.DifferentialGraded.ScalarExtension
