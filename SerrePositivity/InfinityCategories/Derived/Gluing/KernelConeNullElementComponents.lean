module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelConeNullComponents
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelConeNullPrimitive
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModuleConeUnitElement

/-! 指定 kernel 零ホモトピー元の両成分は、実加群円錐の左包含元そのもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
local notation "F" => Morita.kernelTensor R D C M
local notation "KY" => dgGluingKernelObject R C D M Y
local notation "L" => dgGluingKernelConeObject R C D M Y Z f
local notation "rf" => CategoryTheory.Functor.map
  (DGFunctor.onClosed (dgYoneda R D)) (dgGluingConeRightArrow R C D M Y Z f)
local notation "lf" => dgGluingConeLeftArrow R C D M Y Z f

/-- source 成分は、同じ右加群円錐の実左包含元。 -/
lemma dgGluingKernelConeNullElement_source :
    (dgFunctorCommaSourceHomMap R (RightModule R D) (RightModule R C) F KY L).f (-1)
      (dgGluingKernelConeNullElement R C D M Y Z f) = moduleConeInlElement R D rf := by
  have he := congrArg (dgGluingUnitCochainElement _)
    (dgGluingKernelConeNullCochain_source R C D M Y Z f)
  rw [dgGluingUnitCochainElement_postcompose, ← Category.assoc,
    dgGluingIdentity_right] at he
  have hi := (dgYoneda R D).map_id Y.right
  change eId (Complex R) Y.right ≫ yonedaHom R D Y.right Y.right =
    eId (Complex R) (representable R Y.right) at hi
  rw [hi] at he
  exact he.trans (dgGluingModuleConeLeftUnitElement R D rf)

/-- replacement 成分は、同じ左加群円錐の実左包含元。 -/
lemma dgGluingKernelConeNullElement_replacement :
    (dgFunctorCommaReplacementHomMap R (RightModule R D) (RightModule R C) F KY L).f (-1)
      (dgGluingKernelConeNullElement R C D M Y Z f) = moduleConeInlElement R C lf := by
  have he := congrArg (dgGluingUnitCochainElement _)
    (dgGluingKernelConeNullCochain_replacement R C D M Y Z f)
  rw [dgGluingUnitCochainElement_postcompose, ← Category.assoc,
    dgGluingIdentity_left] at he
  have hi := (dgYoneda R C).map_id Y.left
  change eId (Complex R) Y.left ≫ yonedaHom R C Y.left Y.left =
    eId (Complex R) (representable R Y.left) at hi
  rw [hi] at he
  exact he.trans (dgGluingModuleConeLeftUnitElement R C lf)

end SerrePositivity.InfinityCategories
