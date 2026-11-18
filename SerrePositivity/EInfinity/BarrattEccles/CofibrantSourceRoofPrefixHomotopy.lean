module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoofPrefixEndpoints
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofNativeRoofComparison

/-!
# 元の cofibrant comma 全図式の各始点からの実 prefix 円柱

概要：各始点 s からの全射を保ち、同じ右脚と標準評価による native roof の前合成を結ぶ。
方針：元の評価の三角形と全射の弱同値性を Under の全四列円柱へ代入する。
規約：任意可換環・元の全パラメータ・同じ native roof を保持する。
使われ方：基準射側 hR の coherent 合成 prism の各始点からの Hom 写像。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)
  (s : cofibrantSourceRoofProductComma A X Y b)

def cofibrantSourceRoofProductCommaPrefixHomotopy : SSet.Homotopy
    (toUnit (nerve (Under s)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap
      (cofibrantAlgebraRelativeCategory A).weakEquivalences
      ((cofibrantSourceRoofProductCommaRightLeg A X Y b).app s))
    (nerveMap (Under.forget s) ≫ cofibrantSourceRoofProductCommaEvaluationRoofMap A X Y b ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap
        (cofibrantAlgebraRelativeCategory A).weakEquivalences
        ((cofibrantSourceRoofProductCommaEvaluation A X Y b).app s))
        (show (cofibrantAlgebraRelativeCategory A).category from Y)) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.arrowHomotopy
    (cofibrantAlgebraRelativeCategory A).weakEquivalences
    (cofibrantSourceRoofProductCommaDiagram A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation A X Y b)
    (cofibrantSourceRoofProductCommaEvaluation_weak A X Y b)
    (cofibrantSourceRoofProductCommaRightLeg A X Y b)
    (fun f => cofibrantSourceRoofProductCommaDiagram_map_weak A X Y b f) s) rfl
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedRoofMap_eq_precomp]
  exact Category.assoc _ _ _

lemma cofibrantSourceRoofProductCommaPrefixHomotopy_h :
    (cofibrantSourceRoofProductCommaPrefixHomotopy A X Y b s).h =
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.graphHomotopy
      (cofibrantAlgebraRelativeCategory A).weakEquivalences
      (cofibrantSourceRoofProductCommaDiagram A X Y b)
      (cofibrantSourceRoofProductCommaEvaluation A X Y b)
      (cofibrantSourceRoofProductCommaEvaluation_weak A X Y b)
      (cofibrantSourceRoofProductCommaRightLeg A X Y b)
      (fun f => cofibrantSourceRoofProductCommaDiagram_map_weak A X Y b f) s).h ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (cofibrantAlgebraRelativeCategory A).weakEquivalences
      ((cofibrantSourceRoofProductCommaDiagram A X Y b).obj s)
      (show (cofibrantAlgebraRelativeCategory A).category from Y)
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.word :=
  rfl

end SerrePositivity.EInfinity.BarrattEccles
