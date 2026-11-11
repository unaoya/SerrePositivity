module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierTwoSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInitialRefinementCongruence

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
variable (P : Set D) (x : D)

/-- 同じ実二単体と同じ追加閉実辺は、同じ実分母二単体の細分を与える。 -/
lemma dgVerdierTwoSimplexInitialRefinement_congr
    {σ τ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}) _⦋2⦌} (hστ : σ = τ) (q q' : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      (((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ σ.val)).obj 0))
    (s' : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q' ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      (((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ τ.val)).obj 0))
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)
    (hs' : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s').edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)
    (he : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s').edge) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierTwoSimplexInitialRefinement A D P x σ q s hs =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierTwoSimplexInitialRefinement A D P x τ q' s' hs' := by
  apply Subtype.ext
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron_injective
    ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierTwoSimplexInitialRefinement_tetrahedron,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierTwoSimplexInitialRefinement_tetrahedron]
  apply congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_congr
    (congrArg (fun t : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet) _⦋2⦌ =>
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron _ t.val)) hστ) q q' s s' he

end SerrePositivity.InfinityCategories.Project.DerivedCategories
