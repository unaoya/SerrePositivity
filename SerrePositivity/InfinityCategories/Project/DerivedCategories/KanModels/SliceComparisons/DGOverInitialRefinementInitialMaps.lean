module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SliceComparisons.DGOverInitialRefinementReindex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofPointExtendedInitial
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGInitialRefinementInitialMaps

/-! # over 閉始点細分と一般初期順序写像の可換性

概要：零固定・正番号非零の順序写像なら、単射性なしに over 細分と厳密に可換となる。
方針：終点固定延長の同じ条件を、実単体データの一般可換性へ渡す。
規約：非単射零成分・単位成分も保持。使われ方：高次錐の退化条件の保存。
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

/-- 一般の零固定・正番号非零の制限は、同じ実閉射の over 細分と厳密に可換。 -/
lemma dgOverSimplexInitialRefinement_pullback_initial
    (a : Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋n⦌) (h₀ : α.toOrderHom 0 = 0)
    (hz : ∀ i, i ≠ 0 → α.toOrderHom i ≠ 0) (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)).obj 0)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).map α.op (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement A D a σ q s) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement A D a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).map α.op σ) q
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexReindex_source a α σ h₀)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex_injective a
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex_naturality, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement_simplex,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement_simplex]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialMap
  rw [SSet.yonedaEquiv_symm_naturality_left]
  apply congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
  have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_pullback_initial A D
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)) q s (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α).toOrderHom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointExtend_zero α h₀) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointExtend_initial α hz)
  refine hr.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_congr (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex_reindex_data a α σ)
    q q _ _ ?_)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D s _).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D s _).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
