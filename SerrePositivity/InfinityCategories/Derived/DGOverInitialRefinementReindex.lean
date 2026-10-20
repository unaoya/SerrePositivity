module
public import SerrePositivity.InfinityCategories.Derived.DGOverSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Derived.RoofPointExtendedInjection
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementFixedSourceFaces
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementCongruence

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
variable (a : Δ[0] ⟶ dgNerve A D) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
variable (σ : (sliceOver a) _⦋n⦌)

/-- over 制限の回収単体は、元の回収単体の同じ終点固定延長への制限。 -/
lemma roofPointSliceSimplex_reindex_data :
    (SSet.yonedaEquiv (roofPointSliceSimplex a σ)).pullback (PinchedHom.extend α).toOrderHom =
      SSet.yonedaEquiv (roofPointSliceSimplex a ((sliceOver a).map α.op σ)) :=
  (SSet.yonedaEquiv_naturality (PinchedHom.extend α) (roofPointSliceSimplex a σ)).trans
    (congrArg (SSet.yonedaEquiv (X := dgNerve A D)) (roofPointSliceSimplex_naturality a α σ))

/-- 零固定制限では、回収単体の始対象は元の同じ始対象。 -/
lemma dgOverSimplexReindex_source (h₀ : α.toOrderHom 0 = 0) :
    (SSet.yonedaEquiv (roofPointSliceSimplex a σ)).obj 0 =
      (SSet.yonedaEquiv (roofPointSliceSimplex a ((sliceOver a).map α.op σ))).obj 0 :=
  (congrArg (SSet.yonedaEquiv (roofPointSliceSimplex a σ)).obj
    (roofPointExtend_zero α h₀).symm).trans
      (congrArg (fun t : Simplex A D (m + 1) => t.obj 0)
        (roofPointSliceSimplex_reindex_data a α σ))

/-- 同じ実閉射による over 細分は、任意の零固定単射制限と厳密に可換。 -/
lemma dgOverSimplexInitialRefinement_pullback_fixed_zero
    (hα : Function.Injective α.toOrderHom) (h₀ : α.toOrderHom 0 = 0)
    (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
      ((SSet.yonedaEquiv (roofPointSliceSimplex a σ)).obj 0)) :
    (sliceOver a).map α.op (dgOverSimplexInitialRefinement A D a σ q s) =
      dgOverSimplexInitialRefinement A D a ((sliceOver a).map α.op σ) q
        (dgClosedTargetTransport A D s (dgOverSimplexReindex_source a α σ h₀)) := by
  apply roofPointSliceSimplex_injective a
  rw [← roofPointSliceSimplex_naturality, dgOverSimplexInitialRefinement_simplex,
    dgOverSimplexInitialRefinement_simplex]
  unfold dgOverSimplexInitialMap
  rw [SSet.yonedaEquiv_symm_naturality_left]
  apply congrArg (SSet.yonedaEquiv (X := dgNerve A D)).symm
  have hr := dgSimplexInitialRefinement_pullback_fixed_zero A D
    (SSet.yonedaEquiv (roofPointSliceSimplex a σ)) q s (PinchedHom.extend α).toOrderHom
    (roofPointExtend_injective α hα) (roofPointExtend_zero α h₀)
  refine hr.trans (dgSimplexInitialRefinement_congr (roofPointSliceSimplex_reindex_data a α σ)
    q q _ _ ?_)
  exact (dgClosedTargetTransport_edge A D s _).trans (dgClosedTargetTransport_edge A D s _).symm

end SerrePositivity.InfinityCategories
