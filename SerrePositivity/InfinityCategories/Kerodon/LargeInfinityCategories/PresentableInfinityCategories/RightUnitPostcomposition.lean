module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RightUnitCommaVertices

/-!
概要：後合成の随伴の単位を恒等関手で評価し、元の指定単位に戻す。
方針：実ホモトピーの一次単体を比較し、指定単位の Hom 類の回収を使う。
規約：後合成の随伴はコミット済みの公開構成を使う。
使われ方：右単位の coslice 頂点の comma 始対象性の照合。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：後合成の単位ホモトピーを恒等関手で評価した辺は元の単位辺。
方針：二重内部 Hom の評価を全単体で計算する。
規約：単位の元の一次単体を厳密に保持する。
使われ方：後合成の普遍単位と元の実単位の比較。 -/
lemma postcompositionUnit_identity_edge {C D : SSet.{u + 1}}
    {L : C ⟶ D} {R : D ⟶ C} (H : SSet.Homotopy (𝟙 C) (L ≫ R)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.postcompositionUnitHomotopy H C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C))).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).edge := by
  have hI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})) := by
    apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  change (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.postcompositionUnitHomotopy H C).h.app (Opposite.op ⦋1⦌)
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom C).obj C))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C))).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
  rw [hI]
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro c
  rfl

/-- 概要：後合成の指定単位の恒等関手での成分は元の単位の Hom 類。
方針：ホモトピーの評価の公式と同じ辺の回収を使う。
規約：元の全関手圏の h における等式。
使われ方：後合成の comma の普遍矢印を元の指定単位で認識する。 -/
lemma postcompositionUnit_identity_component {C D : SSet.{u + 1}} [Quasicategory C]
    {L : C ⟶ D} {R : D ⟶ C} (H : SSet.Homotopy (𝟙 C) (L ≫ R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent (F := (ihom C).map L) (G := (ihom C).map R)
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.postcompositionUnitHomotopy H C))) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C)) =
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) := by
  rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent (F := (ihom C).map L) (G := (ihom C).map R)
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.postcompositionUnitHomotopy H C))) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C)) =
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.postcompositionUnitHomotopy H C))) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 C)) from rfl]
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomEvaluate_homotopy]
  apply eq_of_heq
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.edgeHom_heq _ _ (postcompositionUnit_identity_edge H)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
