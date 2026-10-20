module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementCongruence

/-! # 元の over 単体と同じ追加実辺による閉細分の厳密一致

概要：元の実 over 単体と追加閉射の実辺が同じなら、細分単体全体も同じである。
方針：回収単体の一般細分の congruence と、over 回収の単射性を使う。
規約：始対象は異なってもよい。使われ方：有限同時細分後の共有面の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の over 単体と追加実辺が一致すれば、全次数の実 over 細分全体が一致する。 -/
lemma dgOverSimplexInitialRefinement_congr (a : Δ[0] ⟶ dgNerve A D) {n : ℕ}
    {σ τ : (sliceOver a) _⦋n⦌} (hστ : σ = τ) (q q' : D)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
      ((SSet.yonedaEquiv (roofPointSliceSimplex a σ)).obj 0))
    (s' : ForgetEnrichment.of (Complex A) q' ⟶ ForgetEnrichment.of (Complex A)
      ((SSet.yonedaEquiv (roofPointSliceSimplex a τ)).obj 0))
    (hs : (dgClosedEdge A D s).edge = (dgClosedEdge A D s').edge) :
    dgOverSimplexInitialRefinement A D a σ q s =
      dgOverSimplexInitialRefinement A D a τ q' s' := by
  apply roofPointSliceSimplex_injective a
  rw [dgOverSimplexInitialRefinement_simplex, dgOverSimplexInitialRefinement_simplex]
  unfold dgOverSimplexInitialMap
  apply congrArg (SSet.yonedaEquiv (X := dgNerve A D)).symm
  exact dgSimplexInitialRefinement_congr
    (congrArg (fun t => SSet.yonedaEquiv (roofPointSliceSimplex a t)) hστ) q q' s s' hs

/-- 同じ実分母部分圏内でも、元の単体と追加実辺だけが細分を決める。 -/
lemma dgVerdierSimplexInitialRefinement_congr [Small.{u} D] [IsDGPretriangulated A D]
    (P : Set D) (x : D) {n : ℕ} {σ τ : (dgVerdierOver A D P x : SSet.{max u v}) _⦋n⦌}
    (hστ : σ = τ) (q q' : D)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
      ((SSet.yonedaEquiv (roofPointSliceSimplex _ σ.val)).obj 0))
    (s' : ForgetEnrichment.of (Complex A) q' ⟶ ForgetEnrichment.of (Complex A)
      ((SSet.yonedaEquiv (roofPointSliceSimplex _ τ.val)).obj 0))
    (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P)
    (hs' : (dgClosedEdge A D s').edge ∈ dgVerdierEdges A D P)
    (he : (dgClosedEdge A D s).edge = (dgClosedEdge A D s').edge) :
    dgVerdierSimplexInitialRefinement A D P x σ q s hs =
      dgVerdierSimplexInitialRefinement A D P x τ q' s' hs' :=
  Subtype.ext (dgOverSimplexInitialRefinement_congr _ (congrArg Subtype.val hστ) q q' s s' he)

end SerrePositivity.InfinityCategories
