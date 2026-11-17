module
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanCofibrant
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.DoubleOpposite

/-!
概要：元のBK重みから、指定された二重反対化した一点重みへの一つの全図式射を選ぶ。
方針：BKの射影cofibrancyと、指定された一点比較の各値の境界右持ち上げ性を使う。
規約：IS-W2 R03aの同じ比較射の構成。Kan係数ごとに選び直さない。
使われ方：全係数図式の切断空間に対する同じ制限写像。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped _root_.Simplicial
variable (J : Type u) [SmallCategory J]

/-- 指定された一点比較を、元の重みと同じ二重反対添字へ移す。 -/
abbrev framedLimitWeightComparison := (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights J).map (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison J)

/-- 元の指定比較は、同じ二重反対図式圏の自由境界に対して右持ち上げ性。 -/
theorem framedLimitWeightComparison_rlp :
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries Jᵒᵖᵒᵖ).rlp (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeightComparison J) := by
  rw [_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries_rlp]
  intro i
  exact _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.comparison_rlp J ((opOpEquivalence J).functor.obj i)

/-- 元のBK重みから指定された一点への唯一の全図式射。 -/
def bkFramedPointMap : bousfieldKanWeight Jᵒᵖᵒᵖ ⟶ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.doubleOpWeights J).obj (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.point J) where
  app i := terminal.from _
  naturality i j f := terminal.hom_ext _ _

/-- 指定した二つの射で作る、元の始対象からの可換四角形。 -/
def bkFramedComparisonSquare :
    CommSq (initial.to (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight J)) (initial.to (bousfieldKanWeight Jᵒᵖᵒᵖ))
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeightComparison J) (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkFramedPointMap J) :=
  ⟨initial.hom_ext _ _⟩

/-- 一つのBK重みから一つの指定重みへの、全係数で共有する比較射。 -/
def bkFramedWeightComparison : bousfieldKanWeight Jᵒᵖᵒᵖ ⟶ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight J := by
  letI bkComparisonLift : HasLiftingProperty (initial.to (bousfieldKanWeight Jᵒᵖᵒᵖ))
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeightComparison J) :=
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanWeight_cofibrant Jᵒᵖᵒᵖ _ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeightComparison_rlp J)
  exact (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkFramedComparisonSquare J).lift

/-- 選んだ同じ比較射は、元の一点への比較を厳密に保つ。 -/
theorem bkFramedWeightComparison_point :
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkFramedWeightComparison J ≫ _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeightComparison J = _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkFramedPointMap J := by
  letI bkComparisonLift : HasLiftingProperty (initial.to (bousfieldKanWeight Jᵒᵖᵒᵖ))
      (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeightComparison J) :=
    _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanWeight_cofibrant Jᵒᵖᵒᵖ _ (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeightComparison_rlp J)
  exact (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkFramedComparisonSquare J).fac_right

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
