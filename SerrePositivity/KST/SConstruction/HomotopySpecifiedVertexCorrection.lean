module
public import SerrePositivity.KST.SConstruction.VertexDiscreteHomotopyCorrection

/-! # 成分の射の類から指定した辺を持つ全体円柱への補正
概要：各頂点で同じ射の類を持つ辺を全体円柱の成分として厳密に指定する。
方針：離散頂点への制限と評価を計算し、固定端点の補正定理に渡す。
規約：全体変換の端点とホモトピー圏での射の類を保持する。
使われ方：局所 Kan な collage 内で元の交差構造射を同時に回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 両端の表示を同時に変えても、指定した二辺の射の類の等号は同値。 -/
lemma diagramEdge_homMk_ofEq_iff {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (e f : X.Edge x y) (hx : x = x') (hy : y = y') :
    SSet.Truncated.HomotopyCategory.homMk (e.ofEq hx hy).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (f.ofEq hx hy).toTruncated ↔
    SSet.Truncated.HomotopyCategory.homMk e.toTruncated =
      SSet.Truncated.HomotopyCategory.homMk f.toTruncated := by
  cases hx
  cases hy
  rfl

/-- 同じ成分の射の類を持つ任意の指定辺へ、全体円柱を厳密に補正できる。 -/
lemma exists_homotopy_specified_vertex_edges {A X : SSet.{u}} [Quasicategory X]
    {F G : A ⟶ X} (H : SSet.Homotopy F G)
    (e : ∀ a : A _⦋0⦌, X.Edge (F.app (Opposite.op ⦋0⦌) a)
      (G.app (Opposite.op ⦋0⦌) a))
    (h : ∀ a, SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H a).toTruncated =
        SSet.Truncated.HomotopyCategory.homMk (e a).toTruncated) :
    ∃ H' : SSet.Homotopy F G,
      (∀ a, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H' a).edge = (e a).edge) ∧
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H') =
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) := by
  let hx (a : A _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A ≫ F).app (Opposite.op ⦋0⦌) a =
      F.app (Opposite.op ⦋0⦌) a := congrArg (F.app _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero a)
  let hy (a : A _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A ≫ G).app (Opposite.op ⦋0⦌) a =
      G.app (Opposite.op ⦋0⦌) a := congrArg (G.app _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero a)
  let e' (a : A _⦋0⦌) := (e a).ofEq (hx a).symm (hy a).symm
  apply exists_vertexDiscrete_homotopy_correction H e'
  intro a
  let l := SSet.Edge.ofTruncated (X := X)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A))).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate (A := A) (X := X) a)))
  let k := SSet.Edge.ofTruncated (X := X)
    ((vertexDiscreteSpecifiedEdge _ _ e').map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate (A := A) (X := X) a)))
  change SSet.Truncated.HomotopyCategory.homMk l.toTruncated =
    SSet.Truncated.HomotopyCategory.homMk k.toTruncated
  apply (diagramEdge_homMk_ofEq_iff l k (hx a) (hy a)).mp
  have hl : l.ofEq (hx a) (hy a) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H a := by
    apply SSet.Edge.ext
    exact vertexDiscrete_restriction_edge_evaluate H a
  have hk : k.ofEq (hx a) (hy a) = e a := by
    apply SSet.Edge.ext
    exact vertexDiscreteSpecifiedEdge_evaluate _ _ e' a
  rw [hl, hk]
  exact h a

end SerrePositivity.KST.SConstruction
