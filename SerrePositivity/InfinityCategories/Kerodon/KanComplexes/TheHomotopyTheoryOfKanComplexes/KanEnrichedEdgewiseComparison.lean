module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseEnrichedFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseOppositeKanComparison
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison

/-!
概要：Kan 値豊穣関手の係数の共通解像と反転を、豊穣な比較にも適用する。
方針：元の Hom を edgewise 解像し、同じ重みの各点で比較の全高次の自然性を使う。
規約：通常の係数反転を元の Hom 上で豊穣関手と仮定しない。
使われ方：strict transport と相対表現の係数比較を全対象で共同実現する。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- Kan 値豊穣関手の係数と Hom パラメーターを同時に共通解像へ移す。 -/
def kanEnrichedFunctorEdgewise {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseEnrichedFunctor F).comp SSet _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanEnriched

/-- 共通解像した Hom 上で、Kan 値豊穣関手の係数を反転する。 -/
def kanEnrichedFunctorOpposite {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject C) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseEnrichedFunctor F).comp SSet _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOppositeKanEnriched

/-- 豊穣自然な比較の共通解像は、解像した Hom の全パラメーターに関して自然。 -/
def KanEnrichedComparison.edgewise {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison (kanEnrichedFunctorEdgewise F) (kanEnrichedFunctorEdgewise G) := by
  refine ⟨fun X ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (η.val X.val), ?_⟩
  intro X Y
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (η.val X.val) ▷
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X.val Y.val)) ≫
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (G.map X.val Y.val) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanEnrichedMap (G.obj X.val).obj (G.obj Y.val).obj) =
    uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (F.map X.val Y.val) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanEnrichedMap (F.obj X.val).obj (F.obj Y.val).obj) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (η.val Y.val)
  rw [uncurry_natural_left, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanEnrichedMap,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseKanEnrichedMap, uncurry_curry, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, f⟩
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparison_app η X.val Y.val (f.app d s) (𝟙 d) (x.app d s)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison export _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedComparison (edgewise)


/-- 豊穣自然な比較は、Hom を解像した上で係数を反転しても豊穣自然。 -/
def KanEnrichedComparison.opposite {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison F G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison (kanEnrichedFunctorOpposite F) (kanEnrichedFunctorOpposite G) := by
  refine ⟨fun X ↦ SSet.opFunctor.map (η.val X.val), ?_⟩
  intro X Y
  change (SSet.opFunctor.map (η.val X.val) ▷
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X.val Y.val)) ≫
      uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (G.map X.val Y.val) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOppositeKanEnrichedMap (G.obj X.val).obj (G.obj Y.val).obj) =
    uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (F.map X.val Y.val) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOppositeKanEnrichedMap (F.obj X.val).obj (F.obj Y.val).obj) ≫
        SSet.opFunctor.map (η.val Y.val)
  rw [uncurry_natural_left, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOppositeKanEnrichedMap,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseOppositeKanEnrichedMap, uncurry_curry, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, f⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparison_app η X.val Y.val
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft (SimplicialCategory.sHom X.val Y.val)).app n f) (𝟙 n) x

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison export _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedComparison (opposite)


end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
