module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceEdges
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn

/-! # 標準単体への元の necklace augmentation の頂点作用
概要：両端点を制限しない全 augmentation が、元の有限頂点順序を保つことを証明する。
方針：全高次単体の頂点制限を回収し、元の全隣接辺の像に単調性を適用する。
規約：元の全単体を保持。使われ方：標準単体の任意の区間への厳密な帰着。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory Opposite _root_.Simplicial SSet

/-- 元の標準単体への augmentation の、元の全頂点への作用。 -/
def necklaceSimplexVertexMap (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {n : ℕ} (f : T.carrier.{u} ⟶ Δ[n]) :
    T.Vertex → Fin (n + 1) :=
  fun v => (f.app _ (T.vertexEquiv.symm v)) 0

/-- 元の任意の単体の各頂点は、同じ augmentation の元の頂点作用を回収する。 -/
lemma necklaceSimplexVertexMap_simplex (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {n m : ℕ}
    (f : T.carrier.{u} ⟶ Δ[n]) (s : T.carrier _⦋m⦌) (i : Fin (m + 1)) :
    (f.app _ s) i = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap T f (s.val i) := by
  have h := f.naturality
    (show ⦋0⦌ ⟶ ⦋m⦌ from SimplexCategory.Hom.mk (OrderHom.const (Fin 1) i)).op
  have hv := congrArg (fun a => (a s) 0) h
  change (f.app _ (T.simplexVertex s i)) 0 = (f.app _ s) i at hv
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.simplexVertex_eq_const] at hv
  exact hv.symm

/-- 元の任意の標準単体への augmentation は、元の有限頂点順序を保つ。 -/
lemma necklaceSimplexVertexMap_monotone (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {n : ℕ}
    (f : T.carrier.{u} ⟶ Δ[n]) : Monotone (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap T f) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  have h := stdSimplex.monotone_apply (f.app _ (T.adjacentEdge i))
    (show (0 : Fin 2) ≤ Fin.last 1 from by decide)
  dsimp only at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap_simplex, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap_simplex] at h
  exact h

/-- 元の augmentation の頂点作用を、同じ有限順序の間の単調写像として読む。 -/
def necklaceSimplexVertexOrderHom (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) {n : ℕ}
    (f : T.carrier.{u} ⟶ Δ[n]) : T.Vertex →o Fin (n + 1) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap T f, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap_monotone T f⟩

/-- 標準単体内の元の全 necklace の始端は、終端以下である。 -/
lemma necklaceInSimplex_first_le_last {n : ℕ} {x y : (Δ[n] : SSet.{u}) _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn Δ[n] x y) : x 0 ≤ y 0 := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap_monotone T.necklace.down T.map
    (show T.necklace.down.first ≤ T.necklace.down.last from Fin.zero_le _)
  change (T.map.app _ T.necklace.down.firstVertex) 0 ≤
    (T.map.app _ T.necklace.down.lastVertex) 0 at h
  rw [T.map_first, T.map_last] at h
  exact h

/-- 標準単体内の逆向きの二端点の間には、元の全 necklace が存在しない。 -/
lemma necklaceInSimplex_isEmpty {n : ℕ} {x y : (Δ[n] : SSet.{u}) _⦋0⦌}
    (h : y 0 < x 0) : IsEmpty (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn Δ[n] x y) :=
  ⟨fun T => (not_le_of_gt h) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInSimplex_first_le_last T)⟩

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInSimplex_first_le_last := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInSimplex_first_le_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceInSimplex_isEmpty := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInSimplex_isEmpty

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceSimplexVertexMap := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceSimplexVertexMap_monotone := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap_monotone

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceSimplexVertexMap_simplex := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap_simplex

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexOrderHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceSimplexVertexOrderHom := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexOrderHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceSimplexVertexMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceSimplexVertexMap._proof_1
