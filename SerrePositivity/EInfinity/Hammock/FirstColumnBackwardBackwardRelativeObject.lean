module

public import SerrePositivity.EInfinity.Hammock.FirstColumnBackwardBackwardData
public import SerrePositivity.EInfinity.Hammock.RelativeAppendParts
public import SerrePositivity.EInfinity.Hammock.BackwardZigzagNativeRelative
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramTotal

/-!
# 元の後向き二列の切断対象の相対自然性

概要：元の底と両係数を送る相対関手と切断関手を厳密に照合する。
方針：指定 Hom の反変作用と残りの語の共変作用の全成分を回収する。
規約：元の両端の等式移送と全縦射を保持する。
使われ方：DK10.3の後向き二列の単体図式への分解。
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
def backwardBackwardRelativeFunctor : backwardBackwardTarget C.weakEquivalences w X Y ⥤
    backwardBackwardTarget D.weakEquivalences w X' Y' :=
  (TwoSidedDiagram.totalFunctor.map (backwardBackwardDataMap w F hX hY)).toFunctor
lemma backwardBackward_relative_head (S : backwardBackwardSource C.weakEquivalences w X Y) :
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
lemma backwardBackward_relative_obj (S : backwardBackwardSource C.weakEquivalences w X Y) :
    backwardBackwardObject D.weakEquivalences w X' Y'
      ((Zigzag.Relative.fixedFunctor F hX hY).obj S) =
    (backwardBackwardRelativeFunctor w F hX hY).obj
      (backwardBackwardObject C.weakEquivalences w X Y S) := by
  apply congrArg₂ (TwoSidedGrothendieck.mk (backwardLeftCoefficient D.weakEquivalences X')
    (backwardRightCoefficient D.weakEquivalences w Y')
    (⟨F.functor.obj (ZigzagAppend.Part.jointFunctor.obj S)⟩ : WideSubcategory D.weakEquivalences))
  · exact backwardBackward_relative_head w F hX hY S
  · exact ZigzagAppend.Part.right_relative_obj F hX hY S

end SerrePositivity.EInfinity.Hammock.FirstColumn
