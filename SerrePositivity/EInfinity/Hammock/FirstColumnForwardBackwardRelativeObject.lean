module

public import SerrePositivity.EInfinity.Hammock.FirstColumnForwardBackwardData
public import SerrePositivity.EInfinity.Hammock.RelativeAppendParts
public import SerrePositivity.EInfinity.Hammock.SingleZigzagRelativeValue
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramTotal

/-!
# 元の混合二方向の全対象の相対自然性

概要：元の係数積と全相対作用素を保持する。
方針：両係数の元の写像と切断の全成分を組にする。
規約：同じ元の graph と augmentation を使う。
使われ方：DK10.3の混合二方向の自然な分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite SimplicialLocalization Zigzag.FirstBoundary
variable {C D : RelativeCategory.{u}} (w : Word) {X Y : C.category} {X' Y' : D.category}
    (F : C ⟶ D) (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
def forwardBackwardRelativeFunctor : forwardBackwardTarget C.weakEquivalences w X Y ⥤
    forwardBackwardTarget D.weakEquivalences w X' Y' :=
  (TwoSidedDiagram.totalFunctor.map (forwardBackwardDataMap w F hX hY)).toFunctor
lemma forwardBackward_relative_head (S : forwardBackwardSource C.weakEquivalences w X Y) :
    Discrete.mk (ForwardZigzag.value (ZigzagAppend.Part.leftObj
      ((Zigzag.Relative.fixedFunctor F hX hY).obj S))) =
    Discrete.mk (eqToHom hX.symm ≫ F.functor.map
      (ForwardZigzag.value (ZigzagAppend.Part.leftObj S))) := by
  apply Discrete.ext
  rw [ZigzagAppend.Part.left_relative_obj F hX hY S]
  simpa only [eqToHom_refl, Category.comp_id] using
    ForwardZigzag.value_relative F hX rfl (ZigzagAppend.Part.leftObj S)
lemma forwardBackward_relative_obj (S : forwardBackwardSource C.weakEquivalences w X Y) :
    forwardBackwardObject D.weakEquivalences w X' Y'
      ((Zigzag.Relative.fixedFunctor F hX hY).obj S) =
    (forwardBackwardRelativeFunctor w F hX hY).obj
      (forwardBackwardObject C.weakEquivalences w X Y S) := by
  apply congrArg₂ (TwoSidedGrothendieck.mk CoefficientProduct.point
    (forwardBackwardRightCoefficient D.weakEquivalences w X' Y')
    (⟨F.functor.obj (ZigzagAppend.Part.jointFunctor.obj S)⟩ :
      WideSubcategory D.weakEquivalences))
  · rfl
  · exact Prod.ext (forwardBackward_relative_head w F hX hY S)
      (ZigzagAppend.Part.right_relative_obj F hX hY S)
end SerrePositivity.EInfinity.Hammock.FirstColumn
