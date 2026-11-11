module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOverSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInitialRefinementDiagonal
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierOver

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 新 over 頂点の構造辺は、追加閉射と元の構造閉射の同じ実合成。 -/
lemma dgOverVertexInitialRefinement_edge (a : Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋0⦌) (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)).obj 0)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement A D a σ q s)).edge =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D (s ≫ (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)).edgeClosed
        0 1 (by decide))).edge := by
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement A D a σ q s)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement_simplex, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialMap, Equiv.apply_symm_apply]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_edge_comp A D _ q s

variable [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 元の over 頂点と追加閉射が実分母なら、新頂点も同じ指定実分母である。 -/
lemma dgOverVertexInitialRefinement_mem (P : Set D) (x : D)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) _⦋0⦌)
    (q : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex _ σ)).obj 0))
    (hσ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGVerdierOverVertex A D P x σ)
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGVerdierOverVertex A D P x (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement A D _ σ q s) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGVerdierOverVertex
  rw [dgOverVertexInitialRefinement_edge]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominator_comp A D P s _ hs
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexEdge_closed_normal A D (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex _ σ))]
  exact hσ

end SerrePositivity.InfinityCategories.Project.DerivedCategories
