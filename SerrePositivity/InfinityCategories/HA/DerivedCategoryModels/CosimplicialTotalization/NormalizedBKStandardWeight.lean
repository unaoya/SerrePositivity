module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.BKWeightComparisonComponents

/-!
# 元の正規化 BK 比較を標準重みへの同じ射でまとめる

概要：bar・over・Mooreの指定された重み射を一つの合成にまとめる。
方針：重みendの反変関手性で元の比較射を因子分解する。
規約：新しい比較射を選ばない。IS-W2 B02の同じ成分照合の分割。
使われ方：HA 1.2.4、Hom–Totの成分を指定重みで評価する入口。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A]

/-- 概要：元の正規化BK重みから標準単体重みへの指定鎖射。
方針：Moore包含・既存over/bar逆射・先頭頂点の比較を合成する。
規約：元の合成順を保持する。使われ方：HA 1.2.4 の指定Hom比較の成分評価。 -/
def normalizedBKStandardWeightMap :
    normalizedBousfieldKanWeight (A := A) ⟶
      (alternatingFaceMapComplex _).obj (standardSimplexWeight (ModuleCat.of A A)) :=
  inclusionOfMooreComplexMap (doubleOppositeOverWeight SimplexCategory (ModuleCat.of A A)) ≫
    (barDoubleOppositeOverChainIso SimplexCategory (ModuleCat.of A A)).inv ≫
    (alternatingFaceMapComplex _).map
      (SimplicialRealization.barStandardWeightComparison (ModuleCat.of A A))

/-- 概要：元のBK Hom比較は同じ標準重み射の前合成である。
方針：既存比較の定義と反変重み関手の合成則。
規約：指定前向き射の厳密な等式。使われ方：HA 1.2.4 のHom–Tot成分の照合。 -/
theorem normalizedBousfieldKanHomComparison_standardWeight
    (X : CosimplicialObject (Complex A)) :
    normalizedBousfieldKanHomComparison X =
      (standardWeightEndTotalIso X).inv ≫
        (linearWeightEndTotalFunctor A (doubleOppositeDiagram X)).map
          (normalizedBKStandardWeightMap A).op ≫
        (weightEndHomIso A normalizedBousfieldKanWeight (doubleOppositeDiagram X)).hom := by
  rw [normalizedBousfieldKanHomComparison,
    bousfieldKanWeightEndTotalComparison, NatTrans.comp_app,
    barWeightEndTotalComparison_app_standard, barToBousfieldKanWeightEndComparison_app]
  simp only [linearWeightEndNormalizationMap, normalizedBKStandardWeightMap,
    op_comp, Functor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
