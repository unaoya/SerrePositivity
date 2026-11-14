module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FaceDegeneracy.NecklaceSimplexVertices

/-! # 元の necklace の bead 内の辺と全隣接辺
概要：内部 joint を跨がない二頂点の間に元の一単体を作る。
方針：順序を保つ二頂点の標準一単体を同じ部分複体へ持ち上げる。
規約：隣接辺を例外なく含む。使われ方：全 necklace 射の頂点作用の単調性。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
namespace NecklaceShape

open CategoryTheory _root_.Simplicial SSet

/-- 元の二頂点 a≤b を結ぶ標準一単体の頂点列。 -/
def edgeOrderHom (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (a b : T.Vertex) (hab : a ≤ b) :
    Fin 2 →o T.Vertex where
  toFun i := if i.val = 0 then a else b
  monotone' i j hij := by
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
    · simp [hi, hj]
    · simpa [hi, hj] using hab
    · have : i.val = 0 := by omega
      exact (hi this).elim
    · simp [hi, hj]

/-- 内部 joint を跨がない元の二頂点の間の、同じ necklace 内の実際の辺。 -/
def edge (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (a b : T.Vertex) (hab : a ≤ b)
    (hj : ∀ k ∈ T.joints, ¬ (a.val < k ∧ k < b.val)) : T.carrier.{u} _⦋1⦌ :=
  ⟨stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk (T.edgeOrderHom a b hab)),
    (T.allows_iff_endpoints (T.edgeOrderHom a b hab)).2 hj⟩

/-- 元の bead 内の辺の始頂点は同じ a。 -/
lemma edge_zero (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (a b : T.Vertex) (hab : a ≤ b)
    (hj : ∀ k ∈ T.joints, ¬ (a.val < k ∧ k < b.val)) :
    (T.edge.{u} a b hab hj).val 0 = a := rfl

/-- 元の bead 内の辺の終頂点は同じ b。 -/
lemma edge_one (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (a b : T.Vertex) (hab : a ≤ b)
    (hj : ∀ k ∈ T.joints, ¬ (a.val < k ∧ k < b.val)) :
    (T.edge.{u} a b hab hj).val (Fin.last 1) = b := rfl

/-- 元の necklace のすべての隣接頂点を結ぶ辺。 -/
def adjacentEdge (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (i : Fin T.vertexMax) : T.carrier.{u} _⦋1⦌ :=
  T.edge i.castSucc i.succ (Fin.castSucc_le_succ i) (by
    intro k hk h
    have h0 : i.val < k := h.1
    have h1 : k < i.val + 1 := h.2
    omega)

/-- 元の隣接辺は同じ前頂点を回収する。 -/
lemma adjacentEdge_zero (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (i : Fin T.vertexMax) :
    (T.adjacentEdge.{u} i).val 0 = i.castSucc := rfl

/-- 元の隣接辺は同じ後頂点を回収する。 -/
lemma adjacentEdge_one (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) (i : Fin T.vertexMax) :
    (T.adjacentEdge.{u} i).val (Fin.last 1) = i.succ := rfl

end NecklaceShape
end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.adjacentEdge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.adjacentEdge := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.adjacentEdge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.adjacentEdge_one := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.adjacentEdge_one

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.adjacentEdge_zero := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.adjacentEdge_zero

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.edge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.edge := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.edge

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.edgeOrderHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.edgeOrderHom := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.edgeOrderHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.edge_one := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.edge_one

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.edge_zero := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.edge_zero

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.adjacentEdge._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.adjacentEdge._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.adjacentEdge._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.adjacentEdge._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.edge._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.edge._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.edgeOrderHom._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.edgeOrderHom._proof_2
