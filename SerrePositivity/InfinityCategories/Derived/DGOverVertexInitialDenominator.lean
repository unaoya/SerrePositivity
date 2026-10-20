module
public import SerrePositivity.InfinityCategories.Derived.DGOverSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementDiagonal
public import SerrePositivity.InfinityCategories.Derived.DGClosedVerdierDenominators
public import SerrePositivity.InfinityCategories.Derived.DGVerdierOver

/-! # 閉始点細分後の over 頂点の構造辺と実分母性

概要：新 over 頂点の構造辺は、追加閉射と元の構造閉射の同じ実合成である。
方針：回収辺の一般閉始点細分の合成公式を使い、実分母の合成閉性を適用する。
規約：元の実辺と指定集合を保持。使われ方：全次元の新 apex の実分母性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 新 over 頂点の構造辺は、追加閉射と元の構造閉射の同じ実合成。 -/
lemma dgOverVertexInitialRefinement_edge (a : Δ[0] ⟶ dgNerve A D)
    (σ : (sliceOver a) _⦋0⦌) (q : D)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
      ((SSet.yonedaEquiv (roofPointSliceSimplex a σ)).obj 0)) :
    (roofPointSliceVertexEdge a (dgOverSimplexInitialRefinement A D a σ q s)).edge =
      (dgClosedEdge A D (s ≫ (SSet.yonedaEquiv (roofPointSliceSimplex a σ)).edgeClosed
        0 1 (by decide))).edge := by
  change SSet.yonedaEquiv (roofPointSliceSimplex a
    (dgOverSimplexInitialRefinement A D a σ q s)) = _
  rw [dgOverSimplexInitialRefinement_simplex, dgOverSimplexInitialMap, Equiv.apply_symm_apply]
  exact dgSimplexInitialRefinement_edge_comp A D _ q s

variable [Small.{u} D] [IsDGPretriangulated A D]

/-- 元の over 頂点と追加閉射が実分母なら、新頂点も同じ指定実分母である。 -/
lemma dgOverVertexInitialRefinement_mem (P : Set D) (x : D)
    (σ : (sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))) _⦋0⦌)
    (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
      ((SSet.yonedaEquiv (roofPointSliceSimplex _ σ)).obj 0))
    (hσ : IsDGVerdierOverVertex A D P x σ)
    (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P) :
    IsDGVerdierOverVertex A D P x (dgOverSimplexInitialRefinement A D _ σ q s) := by
  unfold IsDGVerdierOverVertex
  rw [dgOverVertexInitialRefinement_edge]
  apply dgClosedVerdierDenominator_comp A D P s _ hs
  rw [← dgSimplexEdge_closed_normal A D (SSet.yonedaEquiv (roofPointSliceSimplex _ σ))]
  exact hσ

end SerrePositivity.InfinityCategories
