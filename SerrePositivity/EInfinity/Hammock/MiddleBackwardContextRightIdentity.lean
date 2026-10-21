module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardContextRightReplacement
public import SerrePositivity.EInfinity.Hammock.IdentityColumnOfHEq

/-!
# 任意の前後の語の中の右置換の中央恒等列

概要：元の全体の右置換の中央列は、元の対象と射の意味で恒等列となる。
方針：連結の両端と全列の回収を繰り返し、中央の元の恒等射へ戻す。
規約：前後の語と動く接合対象を保持する。
使われ方：元の eraseInclusion の実際の対象の像の回収。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Context.TrivialCofibration
open CategoryTheory HomotopicalAlgebra ForwardPath

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (a b : Word) (n m : ℕ) (X Y : C)

lemma rightReplacement_identity (S : Objects a b n m X Y) :
    IdentityColumn ((rightReplacement a b n m X Y).obj S) (middleColumn a b n m) := by
  apply IdentityColumn.of_heq_id (E := ((sourceFamily a b n m X Y).left.obj S).obj (Fin.last n))
  all_goals
    dsimp only [rightReplacement, rightDiagram, Zigzag.MovingDiagram.fixedFunctor,
      Zigzag.MovingDiagram.append, MovingFamily.pushoutDiagram, MovingFamily.zigzagObj,
      MiddleBackward.obj, MovingFamily.pushoutFamily, MovingFamily.pushoutMiddle, middleColumn]
  · apply Eq.trans (ZigzagAppend.source_left_eq _ _ _)
    apply Eq.trans (ZigzagAppend.source_right_eq _ _ _)
    dsimp only [Positions.middleColumn]
    apply Eq.trans (ZigzagAppend.source_left_eq _ _ _)
    exact ZigzagAppend.source_right_eq _ _ _
  · apply Eq.trans (ZigzagAppend.target_left_eq _ _ _)
    apply Eq.trans (ZigzagAppend.target_right_eq _ _ _)
    dsimp only [Positions.middleColumn]
    apply Eq.trans (ZigzagAppend.target_left_eq _ _ _)
    exact ZigzagAppend.target_right_eq _ _ _
  · apply HEq.trans (ZigzagAppend.arrow_left_heq _ _ _)
    apply HEq.trans (ZigzagAppend.arrow_right_heq _ _ _)
    dsimp only [Positions.middleColumn]
    apply HEq.trans (ZigzagAppend.arrow_left_heq _ _ _)
    apply HEq.trans (ZigzagAppend.arrow_right_heq _ _ _)
    rfl

end SerrePositivity.EInfinity.Hammock.MiddleBackward.Context.TrivialCofibration
