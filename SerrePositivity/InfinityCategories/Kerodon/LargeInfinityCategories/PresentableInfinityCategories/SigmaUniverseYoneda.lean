module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseYonedaComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaYonedaInfinity

/-!
概要：元の P_Σ を指定された大きい前層圏へ送り、元の Yoneda 全関手を比較する。
方針：元の包含を持ち上げ、指定前層宇宙変更を合成する。
規約：元の包含・元の Yoneda 因子化と全自然同型を保持する。
使われ方：大きい係数前層への全自然変換空間の族。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 元の P_Σ の包含と指定宇宙変更を合成した、一つの大きい前層値関手。 -/
def sigmaUniverseInclusion (C : SSet.{u}) :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity ((SSet.uliftFunctor.{u + 1, u}).obj C) :=
  (SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C) ≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram C

/-- 同じ大きい前層値関手により、元の P_Σ Yoneda は同じ大きい Yoneda と全自然同型。 -/
def sigmaUniverseYonedaIso (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) ≫
      sigmaUniverseInclusion C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap ((SSet.uliftFunctor.{u + 1, u}).obj C)) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) ≫
    ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C) ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram C)) _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap_inclusion]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaInfinityMap_universeIso C

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
