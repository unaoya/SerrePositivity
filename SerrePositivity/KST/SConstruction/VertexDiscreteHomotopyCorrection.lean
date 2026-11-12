module
public import SerrePositivity.KST.SConstruction.VertexDiscreteEdgeClasses

/-! # 元の対象ごとの辺を厳密に回収する全体補正
概要：離散頂点上で指定した変換へ全体の変換を補正し、元の関手空間の射の類を保つ。
方針：座標ごとの射の類の等式を離散部分でまとめ、固定端点の制限の補正を使う。
規約：同じ始点・終点の全体図式を厳密に固定する。
使われ方：元の K の構造射を全対象の縦辺に同時に指定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 離散部分への制限辺の座標評価は、元の全体の円柱の頂点での辺。 -/
lemma vertexDiscrete_restriction_edge_evaluate {A X : SSet.{u}} {F G : A ⟶ X}
    (H : SSet.Homotopy F G) (a : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H a).edge := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro k
    fin_cases k <;> rfl
  change H.h.app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, hi]
  rfl

/-- 対象ごとの指定辺を保つ全体変換が、元の全体変換と同じ射の類で得られる。 -/
lemma exists_vertexDiscrete_homotopy_correction {A X : SSet.{u}} [Quasicategory X]
    {F G : A ⟶ X} (H : SSet.Homotopy F G)
    (e : ∀ a : A _⦋0⦌, X.Edge
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A ≫ F).app (Opposite.op ⦋0⦌) a)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A ≫ G).app (Opposite.op ⦋0⦌) a))
    (h : ∀ a : A _⦋0⦌, SSet.Truncated.HomotopyCategory.homMk
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A))).map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a))) =
      SSet.Truncated.HomotopyCategory.homMk
        ((vertexDiscreteSpecifiedEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A ≫ F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A ≫ G) e).map
          ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a)))) :
    ∃ H' : SSet.Homotopy F G,
      (∀ a : A _⦋0⦌, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H' a).edge = (e a).edge) ∧
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H') =
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) := by
  let k := vertexDiscreteSpecifiedEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A ≫ F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A ≫ G) e
  have hk : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge k) = k := by
    ext
    change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm k.edge))) = k.edge
    rw [curry_uncurry, Equiv.apply_symm_apply]
  have hc := vertexDiscreteFunctorEdge_hom_ext _ _ _ k h
  obtain ⟨H', hr, hh⟩ := exists_fixedEndpoint_restriction_correction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A) H
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge k) (by rw [hk]; exact hc)
  refine ⟨H', ?_, hh⟩
  intro a
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H' (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A)) = k := by
    apply SSet.Truncated.Edge.ext
    change SSet.yonedaEquiv (curry ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A ▷ (Δ[1] : SSet.{u})) ≫ H'.h)) = k.edge
    rw [hr]
    exact congrArg SSet.Truncated.Edge.edge hk
  have hv := congrArg ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a).app (Opposite.op ⦋1⦌))
    (congrArg SSet.Truncated.Edge.edge he)
  have hk0 : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a).app (Opposite.op ⦋1⦌) k.edge = (e a).edge :=
    vertexDiscreteSpecifiedEdge_evaluate _ _ e a
  exact (vertexDiscrete_restriction_edge_evaluate H' a).symm.trans (hv.trans hk0)

end SerrePositivity.KST.SConstruction
