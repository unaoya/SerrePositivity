module
public import SerrePositivity.EInfinity.HomotopyWeight.BousfieldKanChosenComparison
public import SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingContraction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialTerminalWeakContractibility

/-!
概要：一つの指定BK比較射は、元の各値で弱ホモトピー同値。
方針：over圏の元の終対象と一点比較の境界右類から両方の増大の弱同値を得る。
規約：IS-W2 R03aの指定比較の照合。各値のKan性をBK重みに要求しない。
使われ方：射影cofibrant重みのHom不変性を同じ比較射へ適用する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories

/-- 元のBK重みの各値は、元のover圏の終対象により弱可縮。 -/
theorem bousfieldKanWeight_isWeaklyContractible (I : Type u) [SmallCategory I] (i : I) :
    IsWeaklyContractible ((bousfieldKanWeight I).obj i) := by
  exact (nerveVertex_isTerminal (Over.mkIdTerminal (X := i))).isWeaklyContractible

variable (J : Type u) [SmallCategory J]

/-- 指定された二重反対重みの一点比較は、各値で弱ホモトピー同値。 -/
theorem framedLimitWeightComparison_weak (i : Jᵒᵖᵒᵖ) :
    IsWeakHomotopyEquivalence ((framedLimitWeightComparison J).app i) := by
  have hp := (boundaries_rlp Jᵒᵖᵒᵖ).le _ (framedLimitWeightComparison_rlp J) i
  exact FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (SimplicialModel.MonoRightLiftingContraction.localized_isIso _
      (SSet.rlp_monomorphisms.ge _ hp))

/-- 一つの指定BK比較射は、元の全評価で弱ホモトピー同値。 -/
theorem bkFramedWeightComparison_weak (i : Jᵒᵖᵒᵖ) :
    IsWeakHomotopyEquivalence ((bkFramedWeightComparison J).app i) := by
  apply (framedLimitWeightComparison_weak J i).cancel_right
  have he := NatTrans.congr_app (bkFramedWeightComparison_point J) i
  change (bkFramedWeightComparison J).app i ≫ (framedLimitWeightComparison J).app i =
    (bkFramedPointMap J).app i at he
  rw [he]
  have ht : (bkFramedPointMap J).app i = terminal.from ((bousfieldKanWeight Jᵒᵖᵒᵖ).obj i) :=
    terminal.hom_ext _ _
  rw [ht]
  exact bousfieldKanWeight_isWeaklyContractible _ i

end SerrePositivity.EInfinity.HomotopyWeight
