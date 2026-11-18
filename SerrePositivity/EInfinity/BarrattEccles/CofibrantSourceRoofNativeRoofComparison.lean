module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoofSameUniverseComparison
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofProductCone
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofCornerEvaluation

/-!
# 元の comma 全図式の評価 roof と augmentation roof の実比較

概要：元の全 augmentation 三角形を実 cofibrant 圏の四列比較へ代入する。
方針：同じ宇宙の全添字入口を使い、元の二つの roof 写像を anodyne 局所化で比較する。
規約：元の全単体・同じ指定次数・元の右脚・元の弱同値を保つ。
使われ方：基準射側 hR を元の Kan hammock Hom と同じ q の pinched Hom へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite SSet
open SerrePositivity.SimplicialModel
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

lemma cofibrantSourceRoofProductCommaDiagram_map_weak
    {s t : cofibrantSourceRoofProductComma A X Y b} (f : s ⟶ t) :
    (cofibrantAlgebraRelativeCategory A).weakEquivalences
      ((cofibrantSourceRoofProductCommaDiagram A X Y b).map f) :=
  cofibrantDKSourceFrame_map_weak A X ((sourceFrameElementDegree A X Y).map f.left)

def cofibrantSourceRoofProductCommaAugmentationRoofGraphMap :
    nerve (cofibrantSourceRoofProductComma A X Y b) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph (cofibrantAlgebraRelativeCategory A).weakEquivalences _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word
      (show (cofibrantAlgebraRelativeCategory A).category from X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramGraphMap _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram _ (cofibrantSourceRoofProductCommaDiagram A X Y b)
      (cofibrantSourceRoofProductCommaAugmentation A X Y b)
      (cofibrantSourceRoofProductCommaAugmentation_weak A X Y b)
      (cofibrantSourceRoofProductCommaRightLeg A X Y b)
      (fun f => cofibrantSourceRoofProductCommaDiagram_map_weak A X Y b f))

def cofibrantSourceRoofProductCommaAugmentationRoofMap :
    nerve (cofibrantSourceRoofProductComma A X Y b) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (cofibrantAlgebraRelativeCategory A).weakEquivalences
      (show (cofibrantAlgebraRelativeCategory A).category from X)
      (show (cofibrantAlgebraRelativeCategory A).category from Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram _ (cofibrantSourceRoofProductCommaDiagram A X Y b)
      (cofibrantSourceRoofProductCommaAugmentation A X Y b)
      (cofibrantSourceRoofProductCommaAugmentation_weak A X Y b)
      (cofibrantSourceRoofProductCommaRightLeg A X Y b)
      (fun f => cofibrantSourceRoofProductCommaDiagram_map_weak A X Y b f))

def cofibrantSourceRoofProductCommaEvaluationRoofMap :
    nerve (cofibrantSourceRoofProductComma A X Y b) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (cofibrantAlgebraRelativeCategory A).weakEquivalences
      ((cofibrantDKSourceFrame A X).obj (cofibrantSourceRoofDegree A X Y b))
      (show (cofibrantAlgebraRelativeCategory A).category from Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram _ (cofibrantSourceRoofProductCommaDiagram A X Y b)
      (cofibrantSourceRoofProductCommaEvaluation A X Y b)
      (cofibrantSourceRoofProductCommaEvaluation_weak A X Y b)
      (cofibrantSourceRoofProductCommaRightLeg A X Y b)
      (fun f => cofibrantSourceRoofProductCommaDiagram_map_weak A X Y b f))

lemma cofibrantSourceRoofProductCommaEvaluationRoofMap_sourceComparison :
    AnodyneHomotopy.anodyneQ.map (cofibrantSourceRoofProductCommaEvaluationRoofMap A X Y b) =
      AnodyneHomotopy.anodyneQ.map (cofibrantSourceRoofProductCommaAugmentationRoofMap A X Y b) ≫
        AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (cofibrantAlgebraRelativeCategory A).weakEquivalences
            ((cofibrantDKSourceFrameAugmentation A X).app (cofibrantSourceRoofDegree A X Y b)))
          (show (cofibrantAlgebraRelativeCategory A).category from Y)) := by
  have h : (𝟙 (cofibrantSourceRoofProductCommaDiagram A X Y b)) ≫
      cofibrantSourceRoofProductCommaAugmentation A X Y b =
    cofibrantSourceRoofProductCommaEvaluation A X Y b ≫
      (Functor.const (cofibrantSourceRoofProductComma A X Y b)).map
        ((cofibrantDKSourceFrameAugmentation A X).app (cofibrantSourceRoofDegree A X Y b)) := by
    rw [Category.id_comp]
    exact (cofibrantSourceRoofProductCommaAugmentation_triangle A X Y b).symm
  simpa only [Category.id_comp, cofibrantSourceRoofProductCommaEvaluationRoofMap,
    cofibrantSourceRoofProductCommaAugmentationRoofMap] using
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap_sourceComparison
      (cofibrantAlgebraRelativeCategory A).weakEquivalences
      (cofibrantSourceRoofProductCommaDiagram A X Y b)
      (cofibrantSourceRoofProductCommaDiagram A X Y b)
      (cofibrantSourceRoofProductCommaEvaluation A X Y b)
      (cofibrantSourceRoofProductCommaEvaluation_weak A X Y b)
      (cofibrantSourceRoofProductCommaAugmentation A X Y b)
      (cofibrantSourceRoofProductCommaAugmentation_weak A X Y b)
      (𝟙 _) ((cofibrantDKSourceFrameAugmentation A X).app (cofibrantSourceRoofDegree A X Y b))
      (cofibrantSourceRoofProductCommaRightLeg A X Y b) h
      (fun f => cofibrantSourceRoofProductCommaDiagram_map_weak A X Y b f)
      (fun f => cofibrantSourceRoofProductCommaDiagram_map_weak A X Y b f)

end SerrePositivity.EInfinity.BarrattEccles
