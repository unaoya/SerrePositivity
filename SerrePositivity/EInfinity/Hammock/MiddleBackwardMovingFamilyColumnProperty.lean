module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardMovingFamilyDiagram
public import SerrePositivity.EInfinity.Hammock.MiddleBackwardFamilyColumnProperty

/-!
# 動く端点を持つ図式の中央列の性質

概要：元の中央列の性質を、同じ MovingFamily の中央の脚から回収する。
方針：同じ列に沿う連結の二度の等式移送を消去する。
規約：端点が添字とともに動いても、実際の中央の列を使用する。
使われ方：任意の前後の語を保持した左置換の自明性の証明。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingFamily
open CategoryTheory HomotopicalAlgebra ForwardPath

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {A B : D ⥤ C} (F : MovingFamily D C n m A B)

lemma middleColumn_property (P : MorphismProperty C) (d : D) :
    P ((F.zigzagObj d).arrow (Positions.middleColumn n m)) ↔ P (F.middle.app d) := by
  dsimp only [zigzagObj, MiddleBackward.obj, leftBoundaryBlock,
    rightBoundaryBlock, Positions.middleColumn]
  rw [ZigzagAppend.arrow_left_property P, ZigzagAppend.arrow_right_property P]
  rfl

end SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingFamily
