module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedEdgewiseComparison
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramJointComparison

/-!
概要：Kan 値豊穣図式の係数の共通解像と反転、および左右の自然な比較。
方針：各添字の豊穣関手と比較を同じ Hom の解像上へ移し、射影の自然性で束ねる。
規約：対象ごとの同値の集まりではなく、全添字・全対象・全高次で比較する。
使われ方：実際の strict transport と相対表現の共同族の係数を揃える。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 豊穣関手の共通解像から元の係数への比較は、右端射影そのもの。 -/
def kanEnrichedFunctorEdgewiseRightComparison {C : Type v}
    [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedFunctorEdgewise F)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedRight C).comp SSet F) := by
  refine ⟨fun X ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (F.obj X.val).obj, ?_⟩
  intro X Y
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanRightComparison.precompose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseEnrichedFunctor F)).property X Y
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (F.obj X.val).obj ▷ SimplicialCategory.sHom X Y) ≫
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (F.map X.val Y.val) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight ((ihom (F.obj X.val).obj).obj (F.obj Y.val).obj)) =
    uncurry ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedFunctorEdgewise F).map X Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (F.obj Y.val).obj at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_naturality] at h
  exact h

/-- 豊穣関手の共通解像から反転係数への比較は、左端射影そのもの。 -/
def kanEnrichedFunctorEdgewiseLeftComparison {C : Type v}
    [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedFunctorEdgewise F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedFunctorOpposite F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanLeftComparison.precompose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseEnrichedFunctor F)

/-- 全添字の係数と Hom を同時に edgewise 解像した豊穣図式。 -/
def KanEnrichedDiagram.edgewise {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) J where
  obj j := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedFunctorEdgewise (D.obj j)
  map f := (D.map f).edgewise
  map_id j X := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap ((D.map (𝟙 j)).val X.val) = _
    rw [D.map_id]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.map_id _
  map_comp f g X := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap ((D.map (f ≫ g)).val X.val) = _
    rw [D.map_comp]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionFunctor.map_comp _ _

/-- Hom を同じ共通解像に保ち、全添字の Kan 係数を反転した豊穣図式。 -/
def KanEnrichedDiagram.opposite {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) J where
  obj j := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedFunctorOpposite (D.obj j)
  map f := (D.map f).opposite
  map_id j X := by
    change SSet.opFunctor.map ((D.map (𝟙 j)).val X.val) = _
    rw [D.map_id]
    exact SSet.opFunctor.map_id _
  map_comp f g X := by
    change SSet.opFunctor.map ((D.map (f ≫ g)).val X.val) = _
    rw [D.map_comp]
    exact SSet.opFunctor.map_comp _ _

/-- 図式の共通解像から元の係数への、全添字と全対象に自然な右比較。 -/
def KanEnrichedDiagram.edgewiseRightComparison {C : Type v}
    [Category.{u} C] [SimplicialCategory C] {J : Type u} [Category.{u} J]
    (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison D.edgewise (D.precompose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.edgewiseEnrichedRight C)) where
  component j := kanEnrichedFunctorEdgewiseRightComparison (D.obj j)
  naturality f X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight_naturality ((D.map f).val X.val)

/-- 図式の共通解像から反転係数への、全添字と全対象に自然な左比較。 -/
def KanEnrichedDiagram.edgewiseLeftComparison {C : Type v}
    [Category.{u} C] [SimplicialCategory C] {J : Type u} [Category.{u} J]
    (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison D.edgewise D.opposite where
  component j := kanEnrichedFunctorEdgewiseLeftComparison (D.obj j)
  naturality f X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft_naturality ((D.map f).val X.val)

/-- 共通解像の各対象での通常の図式は、元の図式の係数の edgewise 解像。 -/
lemma KanEnrichedDiagram.edgewise_evaluate {C : Type v}
    [Category.{u} C] [SimplicialCategory C] {J : Type u} [Category.{u} J]
    (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J) (X : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) :
    D.edgewise.evaluate X = D.evaluate X.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEdgewiseFunctor := rfl

/-- 反転図式の各対象での通常の図式は、元の図式の係数反転。 -/
lemma KanEnrichedDiagram.opposite_evaluate {C : Type v}
    [Category.{u} C] [SimplicialCategory C] {J : Type u} [Category.{u} J]
    (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J) (X : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) :
    D.opposite.evaluate X = D.evaluate X.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor := rfl

/-- 添字の面・退化を含む任意の制限は、係数の共通解像と厳密に可換。 -/
lemma KanEnrichedDiagram.edgewise_reindex {C : Type v}
    [Category.{u} C] [SimplicialCategory C] {J L : Type u}
    [Category.{u} J] [Category.{u} L] (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J) (k : L ⥤ J) :
    (D.reindex k).edgewise = D.edgewise.reindex k := rfl

/-- 同じ添字の制限は、Hom を共通解像した係数反転とも厳密に可換。 -/
lemma KanEnrichedDiagram.opposite_reindex {C : Type v}
    [Category.{u} C] [SimplicialCategory C] {J L : Type u}
    [Category.{u} J] [Category.{u} L] (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J) (k : L ⥤ J) :
    (D.reindex k).opposite = D.opposite.reindex k := rfl

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
