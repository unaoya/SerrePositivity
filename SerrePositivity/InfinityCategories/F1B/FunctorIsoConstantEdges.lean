module
public import SerrePositivity.InfinityCategories.F1B.HomotopyEdgeNaturality
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
/-!
概要：定値関手と全関手圏で同型な実図式は、全ての実辺を可逆に送る。
方針：同じ辺における実ホモトピーの自然性と、実垂直辺の可逆性を使う。
規約：始域の quasicategory 性は不要。使われ方：実極限錐の同じ各脚の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
/-- 全関手同型は、同じ元の実辺の像の可逆性を反映する。 -/
lemma functorIso_map_isInvertible_of_map {K X : SSet.{u}} [Quasicategory X]
    {f g : K ⟶ X} (e : FunctorIso f g) {a b : K _⦋0⦌}
    (d : Truncated.Edge (X := (truncation 2).obj K) a b)
    (hd : IsInvertibleEdge (d.map ((truncation 2).map g))) :
    IsInvertibleEdge (d.map ((truncation 2).map f)) := by
  let H := FunctorIso.simplicialHomotopy e
  have hA : IsIso (Truncated.HomotopyCategory.homMk
      (simplicialHomotopyVertexEdge H a).toTruncated) :=
    simplicialHomotopyOfFunctorEdge_vertex_isInvertible
      (FunctorIso.edge e) (FunctorIso.edge_isInvertible e) a
  have hB : IsIso (Truncated.HomotopyCategory.homMk
      (simplicialHomotopyVertexEdge H b).toTruncated) :=
    simplicialHomotopyOfFunctorEdge_vertex_isInvertible
      (FunctorIso.edge e) (FunctorIso.edge_isInvertible e) b
  have hD : IsIso (Truncated.HomotopyCategory.homMk (d.map ((truncation 2).map g))) := hd
  have hn := F2.homotopy_edge_naturality H d
  have hC : IsIso (Truncated.HomotopyCategory.homMk (d.map ((truncation 2).map f)) ≫
      Truncated.HomotopyCategory.homMk (simplicialHomotopyVertexEdge H b).toTruncated) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (Truncated.HomotopyCategory.homMk (simplicialHomotopyVertexEdge H b).toTruncated)
/-- 定値と全関手同型で結ばれた実図式は、全ての実辺を可逆に送る。 -/
lemma functorIso_const_map_isInvertible {K X : SSet.{u}} [Quasicategory X]
    {f : K ⟶ X} (x : X _⦋0⦌) (e : FunctorIso f (SSet.const x)) {a b : K _⦋0⦌}
    (d : Truncated.Edge (X := (truncation 2).obj K) a b) :
    IsInvertibleEdge (d.map ((truncation 2).map f)) := by
  apply functorIso_map_isInvertible_of_map e d
  have hi : IsInvertibleEdge (Truncated.Edge.id (X := (truncation 2).obj X) x) := by
    change IsIso (Truncated.HomotopyCategory.homMk
      (Truncated.Edge.id (X := (truncation 2).obj X) x))
    rw [Truncated.HomotopyCategory.homMk_id]
    infer_instance
  exact (isInvertibleEdge_congr (pinchedConstant_one x)).mpr hi
end SerrePositivity.InfinityCategories
