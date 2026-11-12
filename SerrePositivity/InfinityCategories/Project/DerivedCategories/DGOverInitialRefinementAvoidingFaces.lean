module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOverInitialRefinementReindex

/-! # over の閉始点細分は始点を避ける単射制限を保つ

概要：元の始点零を含まない単射制限では、実 over 単体は元のままである。
方針：終点固定延長が零を避けることと、回収単体の制限の保存を接続する。
規約：全次数。使われ方：全正頂点の実分母性と零面の保存。
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

/-- 始点を避ける任意の単射制限では、over 細分後の実単体は元のまま。 -/
lemma dgOverSimplexInitialRefinement_pullback_avoids_zero
    (a : Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋n⦌) (hα : Function.Injective α.toOrderHom)
    (hz : ∀ i, α.toOrderHom i ≠ 0) (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)).obj 0)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).map α.op (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement A D a σ q s) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).map α.op σ := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex_injective a
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex_naturality, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement_simplex]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialMap
  rw [SSet.yonedaEquiv_symm_naturality_left]
  apply (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).injective
  rw [Equiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexInitialRefinement_pullback_avoids_zero A D
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)) q s (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α).toOrderHom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointExtend_injective α hα) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointExtend_avoids_zero α hz)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex_reindex_data a α σ)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
