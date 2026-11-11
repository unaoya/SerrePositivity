module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpaceBinaryTensorProduct
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedProductComparisonEdge
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SpecifiedApexConeRestrictions

/-!
概要：sifted な底上の元の積の全空間 Kan 模型を、native な積錐の頂点にする。
方針：元の比較辺に沿って二項直積の極限錐を輸送し、同じ全錐円柱を保持する。
規約：元の二全空間の図式と比較辺を変更しない。
使われ方：sifted 余極限と二項積の交換の、錐全体の界面。

対応節は Kerodon 9.7（Tag 06ZD）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
variable {E D B : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B]
  (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : D ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]

/-- 元の比較円柱で輸送した、全空間 Kan 模型を頂点とする native な積錐と全比較。 -/
def siftedProductNativeConeTransport :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.SpecifiedApexLimitConeTransport
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceBinaryTensorProductCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject E) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject D))
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (pullback p q))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.totalProductComparisonApexPrism p q) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.specifiedApexLimitConeTransport _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceBinaryTensorProductCone_isLimit _ _) _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.totalProductComparisonApexPrism_zero p q) (by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.totalProductComparisonApexPrism_one]
      apply SSet.yonedaEquiv.injective
      change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex _ = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceBinaryTensorProductCone _ _).vertex
      exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceBinaryTensorProductCone_vertex _ _).symm)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.totalProductComparisonApexPrism_vertical_isInvertible p q)

/-- 元の二つの全空間の図式上で、fiber ごとの積の全空間を頂点とする錐。 -/
def siftedProductNativeCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanBinaryDiagram (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject E) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject D))) :=
  (siftedProductNativeConeTransport p q).cone

/-- 元の全空間 Kan 模型を頂点とする錐は native な積錐。 -/
lemma siftedProductNativeCone_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (siftedProductNativeCone p q) :=
  (siftedProductNativeConeTransport p q).isLimit

/-- 輸送後の頂点は元の fiber ごとの積の全空間 Kan 模型に厳密に一致。 -/
lemma siftedProductNativeCone_vertex :
    (siftedProductNativeCone p q).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject (pullback p q)) := by
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ (siftedProductNativeCone p q).val) = _
  dsimp only [siftedProductNativeCone]
  rw [(siftedProductNativeConeTransport p q).apex_eq, Equiv.apply_symm_apply]

/-- 元の直積の錐への、同じ比較辺を持つ全錐ホモトピー。 -/
def siftedProductNativeConeHomotopy : SSet.Homotopy (siftedProductNativeCone p q).val
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceBinaryTensorProductCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject E) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject D)).val :=
  (siftedProductNativeConeTransport p q).homotopy

/-- 全錐円柱の頂点制限は元の比較辺から作った円柱そのもの。 -/
lemma siftedProductNativeConeHomotopy_apex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫ (siftedProductNativeConeHomotopy p q).h =
      (β_ (Δ[0] : SSet.{u + 1}) (Δ[1] : SSet.{u + 1})).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.totalProductComparisonApexPrism p q :=
  (siftedProductNativeConeTransport p q).apex

/-- 全錐円柱は元の二つの全空間の図式を全時刻で固定する。 -/
lemma siftedProductNativeConeHomotopy_diagram :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫ (siftedProductNativeConeHomotopy p q).h =
      fst _ (Δ[1] : SSet.{u + 1}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanBinaryDiagram (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject E) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanObject D)) :=
  (siftedProductNativeConeTransport p q).diagram

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
