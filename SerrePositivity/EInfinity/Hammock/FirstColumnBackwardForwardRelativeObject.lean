module

public import SerrePositivity.EInfinity.Hammock.FirstColumnBackwardForwardData
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeAppendParts
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.BackwardZigzagNativeRelative
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
def backwardForwardRelativeFunctor : backwardForwardTarget C.weakEquivalences w X Y ⥤
    backwardForwardTarget D.weakEquivalences w X' Y' :=
  (TwoSidedDiagram.totalFunctor.map (backwardForwardDataMap w F hX hY)).toFunctor
lemma backwardForward_relative_head (S : backwardForwardSource C.weakEquivalences w X Y) :
    Discrete.mk (BackwardZigzag.markedHomEquiv (BackwardZigzag.value (ZigzagAppend.Part.leftObj
      ((Zigzag.Relative.fixedFunctor F hX hY).obj S)))) =
    Discrete.mk ((markedCategoryMap F).map
      (BackwardZigzag.markedHomEquiv (BackwardZigzag.value (ZigzagAppend.Part.leftObj S))) ≫
        eqToHom (congrArg (fun T => (⟨T⟩ : WideSubcategory D.weakEquivalences)) hX)) := by
  apply Discrete.ext
  rw [ZigzagAppend.Part.left_relative_obj F hX hY S]
  have he := BackwardZigzag.nativeValue_relative F hX rfl (ZigzagAppend.Part.leftObj S)
  simp only [eqToHom_refl, Category.id_comp] at he
  convert he using 1
lemma backwardForward_relative_obj (S : backwardForwardSource C.weakEquivalences w X Y) :
    backwardForwardObject D.weakEquivalences w X' Y'
      ((Zigzag.Relative.fixedFunctor F hX hY).obj S) =
    (backwardForwardRelativeFunctor w F hX hY).obj
      (backwardForwardObject C.weakEquivalences w X Y S) := by
  apply congrArg₂ (TwoSidedGrothendieck.mk
    (backwardForwardLeftCoefficient D.weakEquivalences w X' Y') CoefficientProduct.point
    (⟨F.functor.obj (ZigzagAppend.Part.jointFunctor.obj S)⟩ :
      WideSubcategory D.weakEquivalences))
  · exact Prod.ext (backwardForward_relative_head w F hX hY S)
      (ZigzagAppend.Part.right_relative_obj F hX hY S)
  · rfl
end SerrePositivity.EInfinity.Hammock.FirstColumn
