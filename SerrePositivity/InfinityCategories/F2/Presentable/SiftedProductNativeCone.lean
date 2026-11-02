module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpaceBinaryTensorProduct
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedProductComparisonEdge
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.SpecifiedApexConeRestrictions

/-!
概要：sifted な底上の元の積の全空間 Kan 模型を、native な積錐の頂点にする。
方針：元の比較辺に沿って二項直積の極限錐を輸送し、同じ全錐円柱を保持する。
規約：元の二全空間の図式と比較辺を変更しない。
使われ方：sifted 余極限と二項積の交換の、錐全体の界面。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {E D B : SSet.{u}} [IsSiftedInfinity B]
  (p : E ⟶ B) [LeftFibration p] (q : D ⟶ B) [LeftFibration q]

/-- 元の比較円柱で輸送した、全空間 Kan 模型を頂点とする native な積錐と全比較。 -/
def siftedProductNativeConeTransport :
    F2.SpecifiedApexLimitConeTransport
      (spaceBinaryTensorProductCone (F2.continuousKanObject E) (F2.continuousKanObject D))
      (SSet.yonedaEquiv.symm (coherentNerveVertex (F2.continuousKanObject (pullback p q))))
      (totalProductComparisonApexPrism p q) :=
  F2.specifiedApexLimitConeTransport _ (spaceBinaryTensorProductCone_isLimit _ _) _ _
    (totalProductComparisonApexPrism_zero p q) (by
      rw [totalProductComparisonApexPrism_one]
      apply SSet.yonedaEquiv.injective
      change coherentNerveVertex _ = (spaceBinaryTensorProductCone _ _).vertex
      exact (spaceBinaryTensorProductCone_vertex _ _).symm)
    (totalProductComparisonApexPrism_vertical_isInvertible p q)

/-- 元の二つの全空間の図式上で、fiber ごとの積の全空間を頂点とする錐。 -/
def siftedProductNativeCone : JoinCone (kanDiagramCoherentNerve
    (kanBinaryDiagram (F2.continuousKanObject E) (F2.continuousKanObject D))) :=
  (siftedProductNativeConeTransport p q).cone

/-- 元の全空間 Kan 模型を頂点とする錐は native な積錐。 -/
lemma siftedProductNativeCone_isLimit : IsLimitCone (siftedProductNativeCone p q) :=
  (siftedProductNativeConeTransport p q).isLimit

/-- 輸送後の頂点は元の fiber ごとの積の全空間 Kan 模型に厳密に一致。 -/
lemma siftedProductNativeCone_vertex :
    (siftedProductNativeCone p q).vertex =
      coherentNerveVertex (F2.continuousKanObject (pullback p q)) := by
  change SSet.yonedaEquiv (joinInl _ _ ≫ (siftedProductNativeCone p q).val) = _
  dsimp only [siftedProductNativeCone]
  rw [(siftedProductNativeConeTransport p q).apex_eq, Equiv.apply_symm_apply]

/-- 元の直積の錐への、同じ比較辺を持つ全錐ホモトピー。 -/
def siftedProductNativeConeHomotopy : SSet.Homotopy (siftedProductNativeCone p q).val
    (spaceBinaryTensorProductCone (F2.continuousKanObject E) (F2.continuousKanObject D)).val :=
  (siftedProductNativeConeTransport p q).homotopy

/-- 全錐円柱の頂点制限は元の比較辺から作った円柱そのもの。 -/
lemma siftedProductNativeConeHomotopy_apex :
    (joinInl _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫ (siftedProductNativeConeHomotopy p q).h =
      (β_ (Δ[0] : SSet.{u + 1}) (Δ[1] : SSet.{u + 1})).hom ≫
        totalProductComparisonApexPrism p q :=
  (siftedProductNativeConeTransport p q).apex

/-- 全錐円柱は元の二つの全空間の図式を全時刻で固定する。 -/
lemma siftedProductNativeConeHomotopy_diagram :
    (joinInr _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫ (siftedProductNativeConeHomotopy p q).h =
      fst _ (Δ[1] : SSet.{u + 1}) ≫ kanDiagramCoherentNerve
        (kanBinaryDiagram (F2.continuousKanObject E) (F2.continuousKanObject D)) :=
  (siftedProductNativeConeTransport p q).diagram

end SerrePositivity.InfinityCategories.HomotopyLimits
