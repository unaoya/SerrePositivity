module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.KernelConeNullElementComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaMinusOnePrimitive

/-! 指定 kernel 境界元の全次数作用の第三成分を、同じ tensor 像の左包含で回収する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "F" => Morita.kernelTensor R D C M
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M)
local notation "KY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M Y
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeObject R C D M Y Z f
local notation "g" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeNullElement R C D M Y Z f
local notation "rf" => CategoryTheory.Functor.map
  (DGFunctor.onClosed (dgYoneda R D)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)

/-- 指定元の像成分は、通常 tensor が同じ実加群円錐左包含を送った元。 -/
lemma dgGluingKernelConeNullElement_image :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R (RightModule R D) (RightModule R C) F KY L).f (-1) g =
      dgModuleFunctorConeInl R D C F rf := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeNullElement_source]
  rfl

variable (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "KX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M X

/-- 第三成分は、元の kernel 第三成分と同じ tensor 左包含の作用の合成の負。 -/
lemma dgGluingKernelConeNullAction_primitive :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingGradedPostcomposition R E KX KY L).f (-1) g).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R (RightModule R D) (RightModule R C) F KX L)
      (by omega : -1 + -1 = -2) =
    -(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R (RightModule R D) (RightModule R C) F KX KY).comp
      ((modulePostcompositionMap R C (representable R X.left)
        ((F).obj (representable R Y.right)) ((F).obj (L).source)).f (-1)
        (dgModuleFunctorConeInl R D C F rf)) (by omega : -1 + -1 = -2) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaMinusOnePost_primitive R (RightModule R D) (RightModule R C)
    F KX KY L g (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeNullElement_primitive R C D M Y Z f)
  rw [dgGluingKernelConeNullElement_image] at h
  exact h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
