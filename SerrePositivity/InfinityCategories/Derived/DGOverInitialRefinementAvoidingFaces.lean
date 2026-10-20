module
public import SerrePositivity.InfinityCategories.Derived.DGOverInitialRefinementReindex

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 始点を避ける任意の単射制限では、over 細分後の実単体は元のまま。 -/
lemma dgOverSimplexInitialRefinement_pullback_avoids_zero
    (a : Δ[0] ⟶ dgNerve A D) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (sliceOver a) _⦋n⦌) (hα : Function.Injective α.toOrderHom)
    (hz : ∀ i, α.toOrderHom i ≠ 0) (q : D)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
      ((SSet.yonedaEquiv (roofPointSliceSimplex a σ)).obj 0)) :
    (sliceOver a).map α.op (dgOverSimplexInitialRefinement A D a σ q s) =
      (sliceOver a).map α.op σ := by
  apply roofPointSliceSimplex_injective a
  rw [← roofPointSliceSimplex_naturality, dgOverSimplexInitialRefinement_simplex]
  unfold dgOverSimplexInitialMap
  rw [SSet.yonedaEquiv_symm_naturality_left]
  apply (SSet.yonedaEquiv (X := dgNerve A D)).injective
  rw [Equiv.apply_symm_apply]
  exact (dgSimplexInitialRefinement_pullback_avoids_zero A D
    (SSet.yonedaEquiv (roofPointSliceSimplex a σ)) q s (PinchedHom.extend α).toOrderHom
    (roofPointExtend_injective α hα) (roofPointExtend_avoids_zero α hz)).trans
      (roofPointSliceSimplex_reindex_data a α σ)

end SerrePositivity.InfinityCategories
