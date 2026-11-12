module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOverSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofPointExtendedInjection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInitialRefinementFixedSourceFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInitialRefinementCongruence

/-! # 実 over 閉始点細分と零固定単射制限の可換性

概要：始点零を保つ任意の単射制限は、同じ実閉射による over 細分と厳密に可換。
方針：元の回収単体への制限を終点固定延長で読み、閉射の等式輸送を実辺で照合する。
規約：対象族の等式は明示する。使われ方：新 apex と全指定面の同じ細分への同定。
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
variable (a : Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
variable (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋n⦌)

/-- over 制限の回収単体は、元の回収単体の同じ終点固定延長への制限。 -/
lemma roofPointSliceSimplex_reindex_data :
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α).toOrderHom =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).map α.op σ)) :=
  (SSet.yonedaEquiv_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)).trans
    (congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex_naturality a α σ))

/-- 零固定制限では、回収単体の始対象は元の同じ始対象。 -/
lemma dgOverSimplexReindex_source (h₀ : α.toOrderHom 0 = 0) :
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)).obj 0 =
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).map α.op σ))).obj 0 :=
  (congrArg (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)).obj
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointExtend_zero α h₀).symm).trans
      (congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D (m + 1) => t.obj 0)
        (roofPointSliceSimplex_reindex_data a α σ))

/-- 同じ実閉射による over 細分は、任意の零固定単射制限と厳密に可換。 -/
lemma dgOverSimplexInitialRefinement_pullback_fixed_zero
    (hα : Function.Injective α.toOrderHom) (h₀ : α.toOrderHom 0 = 0)
    (q : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)).obj 0)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).map α.op (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement A D a σ q s) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement A D a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).map α.op σ) q
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s (dgOverSimplexReindex_source a α σ h₀)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex_injective a
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex_naturality, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement_simplex,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement_simplex]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialMap
  rw [SSet.yonedaEquiv_symm_naturality_left]
  apply congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
  have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_pullback_fixed_zero A D
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)) q s (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α).toOrderHom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointExtend_injective α hα) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointExtend_zero α h₀)
  refine hr.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_congr (roofPointSliceSimplex_reindex_data a α σ)
    q q _ _ ?_)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D s _).trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport_edge A D s _).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
