module
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteLimits.FiberProductCofinality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.Cofinality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.LeftFibrationCofinalPullback
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Filtered.FilteredBinaryDiagonal
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationProduct


/-!
概要：filtered な底上の fiber ごとの積の全空間から、全空間の積への射は right cofinal。
方針：元の二項対角の、二つの left fibration の直積に沿う引き戻しとして表示する。
規約：元の二射影そのものの組を比較射に取る。
使われ方：積の全空間 Kan 比較の弱同値性。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 概要：filtered な底上の二つの left fibration の全空間の積比較は right cofinal。
方針：対角の cofinality を直積の left fibration で引き戻し、元の射へ同型で戻す。
規約：元の二射影の組。使われ方：全空間の積比較の弱同値性。 -/
lemma fiberProductToProduct_isRightCofinal {E D B : SSet.{u}} [Quasicategory B]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : D ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (lift (pullback.fst p q) (pullback.snd p q)) := by
  let h := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.fiberProduct_binaryDiagonal_isPullback p q
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso h.isoPullback.hom).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_pullback_isRightCofinal (p ⊗ₘ q) (lift (𝟙 B) (𝟙 B))
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Filtered.isRightCofinal_binaryDiagonal B))
  rw [h.isoPullback_hom_fst] at hc
  exact hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
