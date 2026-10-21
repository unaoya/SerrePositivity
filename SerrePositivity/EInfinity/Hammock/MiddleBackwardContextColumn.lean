module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardContextRecovery
public import SerrePositivity.EInfinity.Hammock.MiddleBackwardMovingFamilyColumnProperty

/-!
# 任意の前後の語の中の元の中央列の自明性

概要：左置換の中央列は、元の全体の同じ位置で自明 cofibration となる。
方針：前後の語の連結による移送と局所図式の中央列の移送を消去する。
規約：元の全体の語と列の番号を明示し、別の代表に置き換えない。
使われ方：実際の全体の全部分圏への置換の着地。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Context
open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (a b : Word) (n m : ℕ) (X Y : C)

def middleColumn : Fin (wholeWord a b n m).length :=
  ((Positions.middleColumn n m).natAdd a.length).castAdd b.length

variable (cof : MorphismProperty.FunctorialFactorizationData
  (cofibrations C) (trivialFibrations C))

lemma pullback_middle_trivial (S : Zigzag (weakEquivalences C) (wholeWord a b n m) X Y) :
    trivialCofibrations C
      (((pullbackFunctor a b n m X Y cof).obj S).arrow (middleColumn a b n m)) := by
  change trivialCofibrations C ((ZigzagAppend.obj
    (ZigzagAppend.obj ((prefixDiagram a b n m X Y).obj S)
      (((coreFamily a b n m X Y).pullbackFamily cof).zigzagObj S))
    ((suffixDiagram a b n m X Y).obj S)).arrow (middleColumn a b n m))
  dsimp only [middleColumn]
  rw [ZigzagAppend.arrow_left_property (trivialCofibrations C),
    ZigzagAppend.arrow_right_property (trivialCofibrations C)]
  exact (((coreFamily a b n m X Y).pullbackFamily cof).middleColumn_property
    (trivialCofibrations C) S).2
      ((coreFamily a b n m X Y).pullbackMiddle_trivialCofibration cof S)

end SerrePositivity.EInfinity.Hammock.MiddleBackward.Context
