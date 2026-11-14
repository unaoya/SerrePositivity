module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBousfieldKanHomComparison

/-!
# 指定bar・over重み比較の成分

概要：指定自然変換の対象成分を元の重み射の前合成で表す。
方針：既存のHomotopyEquivの前向き射の式を利用する。
規約：IS-W2 B02の因子分解の証明分割。計算上限は変更しない。
使われ方：HA 1.2.4、指定BK Hom比較の同じ前向き射の評価。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
variable {A : Type u} [CommRing A]

/-- 概要：bar前合成の対象成分は元の標準比較の前合成。
方針：既存の前向き射の同定。規約：同じ射。
使われ方：HA 1.2.4 の因子分解の小さい核検査。 -/
theorem barWeightEndTotalComparison_app_standard (X : CosimplicialObject (Complex A)) :
    barWeightEndTotalComparison.app X =
      (standardWeightEndTotalIso X).inv ≫
        (linearWeightEndTotalFunctor A (doubleOppositeDiagram X)).map
          ((alternatingFaceMapComplex _).map
            (SimplicialRealization.barStandardWeightComparison (ModuleCat.of A A))).op :=
  (barWeightEndTotalComparison_app X).trans (barWeightEndTotalHomotopyEquiv_hom X)

/-- 概要：over比較の対象成分は指定鎖同型の逆射の前合成。
方針：評価とwhiskerの定義。規約：元の二重反対圏。
使われ方：HA 1.2.4 の指定重み射の合成。 -/
theorem barToBousfieldKanWeightEndComparison_app (X : CosimplicialObject (Complex A)) :
    barToBousfieldKanWeightEndComparison.app X =
      (linearWeightEndTotalFunctor A (doubleOppositeDiagram X)).map
        (barDoubleOppositeOverChainIso SimplexCategory (ModuleCat.of A A)).inv.op := rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
