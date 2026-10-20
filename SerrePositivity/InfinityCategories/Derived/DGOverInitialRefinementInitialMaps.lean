module
public import SerrePositivity.InfinityCategories.Derived.DGOverInitialRefinementReindex
public import SerrePositivity.InfinityCategories.Derived.RoofPointExtendedInitial
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementInitialMaps

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 一般の零固定・正番号非零の制限は、同じ実閉射の over 細分と厳密に可換。 -/
lemma dgOverSimplexInitialRefinement_pullback_initial
    (a : Δ[0] ⟶ dgNerve A D) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (sliceOver a) _⦋n⦌) (h₀ : α.toOrderHom 0 = 0)
    (hz : ∀ i, i ≠ 0 → α.toOrderHom i ≠ 0) (q : D)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
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
  have hr := dgSimplexInitialRefinement_pullback_initial A D
    (SSet.yonedaEquiv (roofPointSliceSimplex a σ)) q s (PinchedHom.extend α).toOrderHom
    (roofPointExtend_zero α h₀) (roofPointExtend_initial α hz)
  refine hr.trans (dgSimplexInitialRefinement_congr (roofPointSliceSimplex_reindex_data a α σ)
    q q _ _ ?_)
  exact (dgClosedTargetTransport_edge A D s _).trans (dgClosedTargetTransport_edge A D s _).symm

end SerrePositivity.InfinityCategories
