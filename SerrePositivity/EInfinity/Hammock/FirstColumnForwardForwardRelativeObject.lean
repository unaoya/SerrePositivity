module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FirstColumnForwardForwardData
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeAppendParts
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.SingleZigzagRelativeValue
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramTotal

/-!
# 元の前向き二列の切断対象の相対自然性

概要：元の切断対象を相対関手で送る二通りの像が厳密に一致する。
方針：元の底と両係数の比較関手で接合点・残り・先頭 Hom を照合する。
規約：元の固定端点の表示等式を含める。全射の自然性は後続。
使われ方：DK9.4・10.3の全相対作用素の正方形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite Zigzag.FirstBoundary SimplicialLocalization
variable {C D : RelativeCategory.{u}} (w : Word) {X Y : C.category} {X' Y' : D.category}
    (F : C ⟶ D) (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
def forwardForwardRelativeFunctor : forwardForwardTarget C.weakEquivalences w X Y ⥤
    forwardForwardTarget D.weakEquivalences w X' Y' :=
  (TwoSidedDiagram.totalFunctor.map (forwardForwardDataMap w F hX hY)).toFunctor

lemma forwardForward_relative_obj (S : forwardForwardSource C.weakEquivalences w X Y) :
    forwardForwardObject D.weakEquivalences w X' Y'
      ((Zigzag.Relative.fixedFunctor F hX hY).obj S) =
    (forwardForwardRelativeFunctor w F hX hY).obj
      (forwardForwardObject C.weakEquivalences w X Y S) := by
  apply congrArg₂ (TwoSidedGrothendieck.mk (forwardLeftCoefficient D.weakEquivalences w Y')
    (forwardRightCoefficient D.weakEquivalences X')
    (⟨F.functor.obj (ZigzagAppend.Part.jointFunctor.obj S)⟩ :
      WideSubcategory D.weakEquivalences))
  · exact ZigzagAppend.Part.right_relative_obj F hX hY S
  · apply Discrete.ext
    change ForwardZigzag.value (ZigzagAppend.Part.leftObj
      ((Zigzag.Relative.fixedFunctor F hX hY).obj S)) =
        eqToHom hX.symm ≫ F.functor.map (ForwardZigzag.value (ZigzagAppend.Part.leftObj S))
    rw [ZigzagAppend.Part.left_relative_obj F hX hY S]
    simpa only [eqToHom_refl, Category.comp_id] using
      ForwardZigzag.value_relative F hX rfl (ZigzagAppend.Part.leftObj S)
end SerrePositivity.EInfinity.Hammock.FirstColumn
