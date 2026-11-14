module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGInitialRefinementCongruence

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 元の over 単体と追加実辺が一致すれば、全次数の実 over 細分全体が一致する。 -/
lemma dgOverSimplexInitialRefinement_congr (a : Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) {n : ℕ}
    {σ τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋n⦌} (hστ : σ = τ) (q q' : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)).obj 0))
    (s' : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q' ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a τ)).obj 0))
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s').edge) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement A D a σ q s =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement A D a τ q' s' := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex_injective a
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement_simplex, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement_simplex]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialMap
  apply congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_congr
    (congrArg (fun t => SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a t)) hστ) q q' s s' hs

/-- 同じ実分母部分圏内でも、元の単体と追加実辺だけが細分を決める。 -/
lemma dgVerdierSimplexInitialRefinement_congr [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]
    (P : Set D) (x : D) {n : ℕ} {σ τ : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v}) _⦋n⦌}
    (hστ : σ = τ) (q q' : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex _ σ.val)).obj 0))
    (s' : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q' ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex _ τ.val)).obj 0))
    (hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)
    (hs' : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s').edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)
    (he : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s').edge) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexInitialRefinement A D P x σ q s hs =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierSimplexInitialRefinement A D P x τ q' s' hs' :=
  Subtype.ext (dgOverSimplexInitialRefinement_congr _ (congrArg Subtype.val hστ) q q' s s' he)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
