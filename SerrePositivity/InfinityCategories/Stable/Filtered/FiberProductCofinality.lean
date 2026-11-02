module
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FiberProductCofinality
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.F1B.Cofinality.CofinalComposition
public import SerrePositivity.InfinityCategories.F1B.Cofinality.CofinalOpposite
public import SerrePositivity.InfinityCategories.F1B.Cofinality.Cofinality
public import SerrePositivity.InfinityCategories.F1B.Cofinality.LeftFibrationCofinalPullback
public import SerrePositivity.InfinityCategories.Stable.Filtered.FilteredBinaryDiagonal
public import SerrePositivity.InfinityCategories.Core.Filtered.FilteredInfinity
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.LeftFibrationProduct


/-!
概要：filtered な底上の fiber ごとの積の全空間から、全空間の積への射は right cofinal。
方針：元の二項対角の、二つの left fibration の直積に沿う引き戻しとして表示する。
規約：元の二射影そのものの組を比較射に取る。
使われ方：積の全空間 Kan 比較の弱同値性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：filtered な底上の二つの left fibration の全空間の積比較は right cofinal。
方針：対角の cofinality を直積の left fibration で引き戻し、元の射へ同型で戻す。
規約：元の二射影の組。使われ方：全空間の積比較の弱同値性。 -/
lemma fiberProductToProduct_isRightCofinal {E D B : SSet.{u}} [Quasicategory B]
    [IsFilteredInfinity B] (p : E ⟶ B) [LeftFibration p] (q : D ⟶ B) [LeftFibration q] :
    IsRightCofinal (lift (pullback.fst p q) (pullback.snd p q)) := by
  let h := fiberProduct_binaryDiagonal_isPullback p q
  have hc := (isRightCofinal_of_isIso h.isoPullback.hom).comp
    (leftFibration_pullback_isRightCofinal (p ⊗ₘ q) (lift (𝟙 B) (𝟙 B))
      (isRightCofinal_binaryDiagonal B))
  rw [h.isoPullback_hom_fst] at hc
  exact hc

end SerrePositivity.InfinityCategories.F2
