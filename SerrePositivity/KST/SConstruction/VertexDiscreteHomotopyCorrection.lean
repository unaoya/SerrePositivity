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
    (_root_.SerrePositivity.InfinityCategories.Kan.vertexDiscreteEvaluate a).app (Opposite.op ⦋1⦌)
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp H (vertexDiscreteι A))).edge =
        (simplicialHomotopyVertexEdge H a).edge := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro k
    fin_cases k <;> rfl
  change H.h.app (Opposite.op ⦋1⦌)
    (PinchedHom.constant a 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) = _
  rw [pinchedConstant_one, hi]
  rfl

/-- 対象ごとの指定辺を保つ全体変換が、元の全体変換と同じ射の類で得られる。 -/
lemma exists_vertexDiscrete_homotopy_correction {A X : SSet.{u}} [Quasicategory X]
    {F G : A ⟶ X} (H : SSet.Homotopy F G)
    (e : ∀ a : A _⦋0⦌, X.Edge
      ((vertexDiscreteι A ≫ F).app (Opposite.op ⦋0⦌) a)
      ((vertexDiscreteι A ≫ G).app (Opposite.op ⦋0⦌) a))
    (h : ∀ a : A _⦋0⦌, SSet.Truncated.HomotopyCategory.homMk
      ((functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp H (vertexDiscreteι A))).map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kan.vertexDiscreteEvaluate a))) =
      SSet.Truncated.HomotopyCategory.homMk
        ((vertexDiscreteSpecifiedEdge (vertexDiscreteι A ≫ F) (vertexDiscreteι A ≫ G) e).map
          ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kan.vertexDiscreteEvaluate a)))) :
    ∃ H' : SSet.Homotopy F G,
      (∀ a : A _⦋0⦌, (simplicialHomotopyVertexEdge H' a).edge = (e a).edge) ∧
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H') =
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) := by
  let k := vertexDiscreteSpecifiedEdge (vertexDiscreteι A ≫ F) (vertexDiscreteι A ≫ G) e
  have hk : functorEdgeOfSimplicialHomotopy (simplicialHomotopyOfFunctorEdge k) = k := by
    ext
    change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm k.edge))) = k.edge
    rw [curry_uncurry, Equiv.apply_symm_apply]
  have hc := vertexDiscreteFunctorEdge_hom_ext _ _ _ k h
  obtain ⟨H', hr, hh⟩ := exists_fixedEndpoint_restriction_correction (vertexDiscreteι A) H
    (simplicialHomotopyOfFunctorEdge k) (by rw [hk]; exact hc)
  refine ⟨H', ?_, hh⟩
  intro a
  have he : functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp H' (vertexDiscreteι A)) = k := by
    apply SSet.Truncated.Edge.ext
    change SSet.yonedaEquiv (curry ((vertexDiscreteι A ▷ (Δ[1] : SSet.{u})) ≫ H'.h)) = k.edge
    rw [hr]
    exact congrArg SSet.Truncated.Edge.edge hk
  have hv := congrArg ((_root_.SerrePositivity.InfinityCategories.Kan.vertexDiscreteEvaluate a).app (Opposite.op ⦋1⦌))
    (congrArg SSet.Truncated.Edge.edge he)
  have hk0 : (_root_.SerrePositivity.InfinityCategories.Kan.vertexDiscreteEvaluate a).app (Opposite.op ⦋1⦌) k.edge = (e a).edge :=
    vertexDiscreteSpecifiedEdge_evaluate _ _ e a
  exact (vertexDiscrete_restriction_edge_evaluate H' a).symm.trans (hv.trans hk0)

end SerrePositivity.KST.SConstruction
