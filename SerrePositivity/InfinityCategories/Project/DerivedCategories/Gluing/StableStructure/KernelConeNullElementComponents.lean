module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.KernelConeNullComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.KernelConeNullPrimitive
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.ModuleConeUnitElement

/-! 指定 kernel 零ホモトピー元の両成分は、実加群円錐の左包含元そのもの。 -/
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
local notation "KY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelObject R C D M Y
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeObject R C D M Y Z f
local notation "rf" => CategoryTheory.Functor.map
  (DGFunctor.onClosed (dgYoneda R D)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M Y Z f)
local notation "lf" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M Y Z f

/-- source 成分は、同じ右加群円錐の実左包含元。 -/
lemma dgGluingKernelConeNullElement_source :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R (RightModule R D) (RightModule R C) F KY L).f (-1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeNullElement R C D M Y Z f) = moduleConeInlElement R D rf := by
  have he := congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCochainElement _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeNullCochain_source R C D M Y Z f)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCochainElement_postcompose, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentity_right] at he
  have hi := (dgYoneda R D).map_id Y.right
  change eId (Complex R) Y.right ≫ yonedaHom R D Y.right Y.right =
    eId (Complex R) (representable R Y.right) at hi
  rw [hi] at he
  exact he.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleConeLeftUnitElement R D rf)

/-- replacement 成分は、同じ左加群円錐の実左包含元。 -/
lemma dgGluingKernelConeNullElement_replacement :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R (RightModule R D) (RightModule R C) F KY L).f (-1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeNullElement R C D M Y Z f) = moduleConeInlElement R C lf := by
  have he := congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCochainElement _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelConeNullCochain_replacement R C D M Y Z f)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCochainElement_postcompose, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentity_left] at he
  have hi := (dgYoneda R C).map_id Y.left
  change eId (Complex R) Y.left ≫ yonedaHom R C Y.left Y.left =
    eId (Complex R) (representable R Y.left) at hi
  rw [hi] at he
  exact he.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingModuleConeLeftUnitElement R C lf)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
