module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierBoundaryRefinedSimplex
public import SerrePositivity.InfinityCategories.Derived.DGOverInitialRefinementCongruence

/-! # 一般有限境界充填の同じ共有面の厳密一致

概要：元の指定錐面と追加実閉辺が同じなら、二つの回収単体の対応する面も厳密に同じ。
方針：両正番号面を元の同じ境界面の細分へ戻し、実辺だけで決まる congruence を使う。
規約：別の充填・別の型付き追加射を許す。使われ方：有限図式の次数帰納での貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 二つの元の正番号錐面と追加実辺が同じなら、細分後の二つの実面も厳密に一致する。 -/
lemma dgVerdierBoundaryRefinedSimplex_commonFace_eq (P : Set D) (x : D) {n : ℕ}
    (B B' : (∂Δ[n + 1] : SSet.{max u v}) ⟶ (dgVerdierOver A D P x : SSet))
    (q q' : D)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
      ((HornData.knownData (dgVerdierBoundaryHorn A D P x B)).obj 0))
    (s' : ForgetEnrichment.of (Complex A) q' ⟶ ForgetEnrichment.of (Complex A)
      ((HornData.knownData (dgVerdierBoundaryHorn A D P x B')).obj 0))
    (F F' : Δ[n + 2] ⟶ dgNerve A D)
    (hF : (horn (n + 2) (Fin.last (n + 2))).ι ≫ F =
      dgGeneralLastHornSourceRefinement (dgVerdierBoundaryHorn A D P x B) q s)
    (hF' : (horn (n + 2) (Fin.last (n + 2))).ι ≫ F' =
      dgGeneralLastHornSourceRefinement (dgVerdierBoundaryHorn A D P x B') q' s')
    (hs : (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P)
    (hs' : (dgClosedEdge A D s').edge ∈ dgVerdierEdges A D P)
    (j k : Fin (n + 2)) (hj : j ≠ 0) (hk : k ≠ 0)
    (hface : SSet.yonedaEquiv (boundary.ι j ≫ B) = SSet.yonedaEquiv (boundary.ι k ≫ B'))
    (he : (dgClosedEdge A D s).edge = (dgClosedEdge A D s').edge) :
    (dgVerdierOver A D P x : SSet).δ j
        (dgVerdierBoundaryRefinedSimplex A D P x B q s F hF hs) =
      (dgVerdierOver A D P x : SSet).δ k
        (dgVerdierBoundaryRefinedSimplex A D P x B' q' s' F' hF' hs') := by
  rw [dgVerdierBoundaryRefinedSimplex_face_positive A D P x B q s F hF hs j hj,
    dgVerdierBoundaryRefinedSimplex_face_positive A D P x B' q' s' F' hF' hs' k hk]
  apply dgVerdierSimplexInitialRefinement_congr P x hface q q'
  exact (dgClosedTargetTransport_edge A D s _).trans
    (he.trans (dgClosedTargetTransport_edge A D s' _).symm)

end SerrePositivity.InfinityCategories
