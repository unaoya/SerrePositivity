module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardPositions
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendArrowProperty

/-!
# 中央の実際の列とブロック図式の中央の脚の性質

概要：中央の元の列の任意の射の性質は、同じ図式の中央の自然な脚の性質と同値。
方針：連結の同じ元の左列・右列の移送を二度消す。
規約：中央の自明性を、別の代表の性質で置き換えない。
使われ方：実際の固定語の全部分圏への左置換の着地。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Family
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra ForwardPath

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {X Y : C} (F : Family D C n m X Y)

lemma middleColumn_property (P : MorphismProperty C) (d : D) :
    P ((F.zigzagFunctor.obj d).arrow (Positions.middleColumn n m)) ↔ P (F.middle.app d) := by
  dsimp only [zigzagFunctor, zigzagObj, MiddleBackward.obj, leftBoundaryBlock,
    rightBoundaryBlock, Positions.middleColumn]
  rw [ZigzagAppend.arrow_left_property P, ZigzagAppend.arrow_right_property P]
  rfl

end SerrePositivity.EInfinity.Hammock.MiddleBackward.Family
