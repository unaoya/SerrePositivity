module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitSixTriangleVertices
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitSixTriangleCancellation
/-! # 五頂点上の実六二単体と合成構造

概要：五頂点を保持する六片を、同じ二単体を持つ六つの型付き合成構造へ接続する。
方針：各面を実辺として保持し、共有面の等式を辺の等式へ移す。
規約：二単体の充填や辺の代表を選び直さない。
使われ方：実単位閉路の零性だけから係数六角形を得る。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet
open scoped _root_.Simplicial

structure DGGluingUnitSixTriangleDiagram (Z : SSet.{u}) (a b c d e : Z _⦋0⦌) where
  diagram : Fin 6 → ((Δ[2] : SSet.{u}) ⟶ Z)
  vertices : ∀ i j, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleVertex (diagram i) j =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitSixTriangleVertexPattern a b c d e i j
  first_diagonal : stdSimplex.δ (1 : Fin 3) ≫ diagram 0 =
    stdSimplex.δ (1 : Fin 3) ≫ diagram 1
  last_diagonal : stdSimplex.δ (1 : Fin 3) ≫ diagram 2 =
    stdSimplex.δ (1 : Fin 3) ≫ diagram 3
  first_bridge : stdSimplex.δ (2 : Fin 3) ≫ diagram 1 =
    stdSimplex.δ (2 : Fin 3) ≫ diagram 5
  last_bridge : stdSimplex.δ (0 : Fin 3) ≫ diagram 3 =
    stdSimplex.δ (0 : Fin 3) ≫ diagram 5
  coefficient_first : stdSimplex.δ (0 : Fin 3) ≫ diagram 1 =
    stdSimplex.δ (0 : Fin 3) ≫ diagram 4
  coefficient_last : stdSimplex.δ (2 : Fin 3) ≫ diagram 3 =
    stdSimplex.δ (2 : Fin 3) ≫ diagram 4

def dgGluingUnitSixTriangleDiagramOfEdges {Z : SSet.{u}} {a b d e : Z _⦋0⦌}
    (T : Fin 6 → ((Δ[2] : SSet.{u}) ⟶ Z))
    (df : Truncated.Edge (X := (truncation 2).obj Z) a b)
    (dl : Truncated.Edge (X := (truncation 2).obj Z) d e)
    (k : Truncated.Edge (X := (truncation 2).obj Z) d b)
    (hdf : SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ T 0) = df.edge)
    (hdl : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ T 2) = dl.edge)
    (hk : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ T 4) = k.edge)
    (h01 : stdSimplex.δ (1 : Fin 3) ≫ T 0 = stdSimplex.δ (1 : Fin 3) ≫ T 1)
    (h23 : stdSimplex.δ (1 : Fin 3) ≫ T 2 = stdSimplex.δ (1 : Fin 3) ≫ T 3)
    (h15 : stdSimplex.δ (2 : Fin 3) ≫ T 1 = stdSimplex.δ (2 : Fin 3) ≫ T 5)
    (h35 : stdSimplex.δ (0 : Fin 3) ≫ T 3 = stdSimplex.δ (0 : Fin 3) ≫ T 5)
    (h14 : stdSimplex.δ (0 : Fin 3) ≫ T 1 = stdSimplex.δ (0 : Fin 3) ≫ T 4)
    (h34 : stdSimplex.δ (2 : Fin 3) ≫ T 3 = stdSimplex.δ (2 : Fin 3) ≫ T 4) :
    DGGluingUnitSixTriangleDiagram Z a b (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleVertex (T 4) 1) d e where
  diagram := T
  vertices := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitSixTriangle_vertices T df dl k hdf hdl hk h01 h23 h15 h35 h14 h34
  first_diagonal := h01
  last_diagonal := h23
  first_bridge := h15
  last_bridge := h35
  coefficient_first := h14
  coefficient_last := h34

namespace DGGluingUnitSixTriangleDiagram
variable {Z : SSet.{u}} {a b c d e : Z _⦋0⦌}
  (P : DGGluingUnitSixTriangleDiagram Z a b c d e)

def edge (i : Fin 6) (j : Fin 3) : Truncated.Edge (X := (truncation 2).obj Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitSixTriangleVertexPattern a b c d e i (![1,0,0] j))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitSixTriangleVertexPattern a b c d e i (![2,2,1] j)) where
  edge := SSet.yonedaEquiv (stdSimplex.δ j ≫ P.diagram i)
  src_eq := by
    change Z.δ 1 _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleFace_source, P.vertices]
  tgt_eq := by
    change Z.δ 0 _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleFace_target, P.vertices]

def comp (i : Fin 6) : Truncated.Edge.CompStruct (P.edge i 2) (P.edge i 0)
    (P.edge i 1) where
  simplex := SSet.yonedaEquiv (P.diagram i)
  d₂ := by change Z.δ 2 _ = _; rw [← stdSimplex.yonedaEquiv_δ_comp]; rfl
  d₀ := by change Z.δ 0 _ = _; rw [← stdSimplex.yonedaEquiv_δ_comp]; rfl
  d₁ := by change Z.δ 1 _ = _; rw [← stdSimplex.yonedaEquiv_δ_comp]; rfl

lemma first_diagonal_edge : P.edge 0 1 = P.edge 1 1 := by
  ext; exact congrArg SSet.yonedaEquiv P.first_diagonal
lemma last_diagonal_edge : P.edge 2 1 = P.edge 3 1 := by
  ext; exact congrArg SSet.yonedaEquiv P.last_diagonal
lemma first_bridge_edge : P.edge 1 2 = P.edge 5 2 := by
  ext; exact congrArg SSet.yonedaEquiv P.first_bridge
lemma last_bridge_edge : P.edge 3 0 = P.edge 5 0 := by
  ext; exact congrArg SSet.yonedaEquiv P.last_bridge
lemma coefficient_first_edge : P.edge 1 0 = P.edge 4 0 := by
  ext; exact congrArg SSet.yonedaEquiv P.coefficient_first
lemma coefficient_last_edge : P.edge 3 2 = P.edge 4 2 := by
  ext; exact congrArg SSet.yonedaEquiv P.coefficient_last
end DGGluingUnitSixTriangleDiagram
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
