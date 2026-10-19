module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierTwoSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementCongruence

/-! # 実分母二単体の閉始点細分は元の単体と閉実辺だけで決まる

概要：異なる型付き始対象・閉射でも、元の二単体と追加閉実辺が同じなら細分全体が同じ。
方針：回収四面体の単射性と一般閉始点細分の合同性で比較する。
規約：分母性の証明に依存しない。使われ方：有限二単体図式の共通辺錐の厳密一致。
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
variable [Small.{u} D] [IsDGPretriangulated A D]
variable (P : Set D) (x : D)

/-- 同じ実二単体と同じ追加閉実辺は、同じ実分母二単体の細分を与える。 -/
lemma dgVerdierTwoSimplexInitialRefinement_congr
    {σ τ : (dgVerdierOver A D P x : SSet.{max u v}) _⦋2⦌} (hστ : σ = τ) (q q' : D)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
      (((SSet.yonedaEquiv (X := dgNerve A D)) (roofPointSliceTetrahedron _ σ.val)).obj 0))
    (s' : ForgetEnrichment.of (Complex A) q' ⟶ ForgetEnrichment.of (Complex A)
      (((SSet.yonedaEquiv (X := dgNerve A D)) (roofPointSliceTetrahedron _ τ.val)).obj 0))
    (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P)
    (hs' : (dgClosedEdge A D s').edge ∈ dgVerdierEdges A D P)
    (he : (dgClosedEdge A D s).edge = (dgClosedEdge A D s').edge) :
    dgVerdierTwoSimplexInitialRefinement A D P x σ q s hs =
      dgVerdierTwoSimplexInitialRefinement A D P x τ q' s' hs' := by
  apply Subtype.ext
  apply roofPointSliceTetrahedron_injective
    ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))
  rw [dgVerdierTwoSimplexInitialRefinement_tetrahedron,
    dgVerdierTwoSimplexInitialRefinement_tetrahedron]
  apply congrArg (SSet.yonedaEquiv (X := dgNerve A D)).symm
  exact dgSimplexInitialRefinement_congr
    (congrArg (fun t : (dgVerdierOver A D P x : SSet) _⦋2⦌ =>
      SSet.yonedaEquiv (roofPointSliceTetrahedron _ t.val)) hστ) q q' s s' he

end SerrePositivity.InfinityCategories
