module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.UniverseYonedaJoint
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.GrothendieckConstruction.PresheafUniverseDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorSpaceCurrying

/-!
概要：指定された前層の宇宙変更は、元の全 Yoneda 関手を全自然同型として保つ。
方針：元の二変数 Hom 比較を curry し、同じ前層宇宙変更の全評価の式へ同定する。
規約：元の Yoneda 全写像と指定宇宙変更を保持する。
使われ方：元の大きい係数前層への自然変換空間の全族と、元の延長の Hom 全族の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable (C : SSet.{u}) [Quasicategory C]

omit [Quasicategory C] in
/-- 同じ共同 Hom の底比較は、元の前層の宇宙変更に現れる指定比較の合成。 -/
lemma homInfinityUniverseBaseMap_equation :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseYonedaJoint.homInfinityUniverseBaseMap C =
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso.{u, u + 1} C).inv ▷
        (SSet.uliftFunctor.{u + 2, u + 1}).obj ((SSet.uliftFunctor.{u + 1, u}).obj C)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u + 1, u + 2}
        ((SSet.uliftFunctor.{u + 1, u}).obj C.op)
        ((SSet.uliftFunctor.{u + 1, u}).obj C)).inv ≫
      (SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1} C.op C).inv := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 元の Yoneda の指定宇宙変更の共同評価は、同じ小さい共同 Hom の宇宙変更。 -/
lemma yonedaInfinityMap_universe_uncurry :
    uncurry ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram C) =
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseYonedaJoint.homInfinityUniverseBaseMap C ≫
      (SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram.{u} := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram]
  rw [← Category.assoc, ← Category.assoc, uncurry_pre_app, uncurry_natural_right,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftInternalHomComparison_map_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_uncurry,
    homInfinityUniverseBaseMap_equation]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation]
  simp only [Functor.map_comp, Category.assoc]

/-- 指定前層宇宙変更をした元の Yoneda 全関手は、持ち上げた元の圏の Yoneda と自然同型。 -/
def yonedaInfinityMap_universeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap ((SSet.uliftFunctor.{u + 1, u}).obj C)) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorIso.curry (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseYonedaJoint.homInfinityJointUniverseIso C).symm
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (curry (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseYonedaJoint.homInfinityUniverseBaseMap C ≫
    (SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity C) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram.{u})) _ at e
  rw [← yonedaInfinityMap_universe_uncurry, curry_uncurry] at e
  exact e

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
