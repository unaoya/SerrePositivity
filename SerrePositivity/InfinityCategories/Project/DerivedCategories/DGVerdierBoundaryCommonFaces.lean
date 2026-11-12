module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierBoundaryRefinedSimplex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOverInitialRefinementCongruence

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 二つの元の正番号錐面と追加実辺が同じなら、細分後の二つの実面も厳密に一致する。 -/
lemma dgVerdierBoundaryRefinedSimplex_commonFace_eq (P : Set D) (x : D) {n : ℕ}
    (B B' : (∂Δ[n + 1] : SSet.{max u v}) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet))
    (q q' : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryHorn A D P x B)).obj 0))
    (s' : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q' ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryHorn A D P x B')).obj 0))
    (F F' : Δ[n + 2] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (hF : (horn (n + 2) (Fin.last (n + 2))).ι ≫ F =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryHorn A D P x B) q s)
    (hF' : (horn (n + 2) (Fin.last (n + 2))).ι ≫ F' =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryHorn A D P x B') q' s')
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)
    (hs' : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s').edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)
    (j k : Fin (n + 2)) (hj : j ≠ 0) (hk : k ≠ 0)
    (hface : SSet.yonedaEquiv (boundary.ι j ≫ B) = SSet.yonedaEquiv (boundary.ι k ≫ B'))
    (he : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s').edge) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ j
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryRefinedSimplex A D P x B q s F hF hs) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet).δ k
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryRefinedSimplex A D P x B' q' s' F' hF' hs') := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryRefinedSimplex_face_positive A D P x B q s F hF hs j hj,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierBoundaryRefinedSimplex_face_positive A D P x B' q' s' F' hF' hs' k hk]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexInitialRefinement_congr P x hface q q'
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D s _).trans
    (he.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D s' _).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
