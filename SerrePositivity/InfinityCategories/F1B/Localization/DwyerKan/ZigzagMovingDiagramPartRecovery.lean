module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingDiagramParts
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendPartRecovery
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingDiagramExt
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingDiagramAppend

/-!
# 前後の部分図式から元の全図式を回収する

概要：左右の部分図式を貼り直すと、元の図式そのものに戻る。
方針：対象の回収に加え、全縦射の各成分を左右の位置で照合する。
規約：動く接合点の元の縦射と全ての射の合成を保持する。
使われ方：局所置換の図式を元の全体へ戻す厳密な同定。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
open CategoryTheory

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {a b : Word} {A B : D ⥤ C}
  (F : MovingDiagram D C W (Word.append a b) A B)

lemma append_parts : F.leftPart.append F.rightPart = F := by
  apply ext _ _ (fun d => ZigzagAppend.Part.rebuilt_eq (F.obj d))
  intro d d' f j
  by_cases hj : j.val ≤ a.length
  · let i := ZigzagAppend.leftIndex j hj
    have hi : Word.leftVertex a b i = j := Fin.ext rfl
    rw [← hi]
    apply HEq.trans (ZigzagAppend.Moving.app_left_heq
      (F.leftPart.map f) (F.rightPart.map f) i)
    rfl
  · let i := ZigzagAppend.rightIndex j hj
    have hi : Word.rightVertex a b i = j := by
      apply Fin.ext
      change a.length + (j.val - a.length) = j.val
      omega
    rw [← hi]
    apply HEq.trans (ZigzagAppend.Moving.app_right_heq
      (F.leftPart.map f) (F.rightPart.map f)
      ((F.leftPart.last f).trans (F.rightPart.first f).symm) i)
    rfl

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
