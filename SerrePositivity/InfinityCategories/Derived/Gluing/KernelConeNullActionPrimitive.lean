module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelConeNullElementComponents
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaMinusOnePrimitive

/-! 指定 kernel 境界元の全次数作用の第三成分を、同じ tensor 像の左包含で回収する。 -/
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
local notation "E" => DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M)
local notation "KY" => dgGluingKernelObject R C D M Y
local notation "L" => dgGluingKernelConeObject R C D M Y Z f
local notation "g" => dgGluingKernelConeNullElement R C D M Y Z f
local notation "rf" => CategoryTheory.Functor.map
  (DGFunctor.onClosed (dgYoneda R D)) (dgGluingConeRightArrow R C D M Y Z f)

/-- 指定元の像成分は、通常 tensor が同じ実加群円錐左包含を送った元。 -/
lemma dgGluingKernelConeNullElement_image :
    (dgFunctorCommaImageHomMap R (RightModule R D) (RightModule R C) F KY L).f (-1) g =
      dgModuleFunctorConeInl R D C F rf := by
  rw [dgFunctorCommaImageHomMap, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    dgGluingKernelConeNullElement_source]
  rfl

variable (X : DGGluingObject R C D M)
local notation "KX" => dgGluingKernelObject R C D M X

/-- 第三成分は、元の kernel 第三成分と同じ tensor 左包含の作用の合成の負。 -/
lemma dgGluingKernelConeNullAction_primitive :
    ((dgGluingGradedPostcomposition R E KX KY L).f (-1) g).comp
      (dgFunctorCommaPrimitive R (RightModule R D) (RightModule R C) F KX L)
      (by omega : -1 + -1 = -2) =
    -(dgFunctorCommaPrimitive R (RightModule R D) (RightModule R C) F KX KY).comp
      ((modulePostcompositionMap R C (representable R X.left)
        ((F).obj (representable R Y.right)) ((F).obj (L).source)).f (-1)
        (dgModuleFunctorConeInl R D C F rf)) (by omega : -1 + -1 = -2) := by
  have h := dgGluingCommaMinusOnePost_primitive R (RightModule R D) (RightModule R C)
    F KX KY L g (dgGluingKernelConeNullElement_primitive R C D M Y Z f)
  rw [dgGluingKernelConeNullElement_image] at h
  exact h

end SerrePositivity.InfinityCategories
