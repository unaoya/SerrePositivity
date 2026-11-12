module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedBoundaryFaceAgreement

/-!
概要：weighted nerve の全境界は、最後の係数の指定境界充填から充填できる。
方針：元の最後の面に指定係数充填を追加し、全ての面との一致を検査する。
規約：指定された充填そのものを保持。使われ方：weighted 比較の相対境界充填。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 最後の係数の実際の境界充填を、同じ元の全図式の境界充填へ戻す。 -/
lemma exists_weightedBoundary_lift_with_coefficient {I : Type u} [Category.{u} I]
    (F : I ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows I (n + 1))
    (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
      (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm σ)
    (H : (Δ[n + 1] : SSet.{u}) ⟶ F.obj (σ.obj (Fin.last (n + 1))))
    (hH : (boundary (n + 1)).ι ≫ H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ a (boundary (n + 1)).ι ha) :
    ∃ ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight (n + 1) ⟶ σ ⋙ F,
      (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm
        (⟨σ, ψ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F (n + 1)) = a ∧
      ψ.app (Fin.last (n + 1)) = H := by
  let r := boundary.ι (Fin.last (n + 1))
  let α := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)
  have hb := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedBoundaryFace_base F σ a ha (Fin.last (n + 1))).trans
    (congrArg (fun q ↦ (SimplexCategory.toCat.map q).toFunctor ⋙ σ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_eq_lastFace n).symm)
  let τ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexDiagram F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNervePrefixFunctor n ⋙ σ)
    (SSet.yonedaEquiv (r ≫ a)) hb
  have hτ : (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNervePrefixFunctor n ⋙ σ, τ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n) =
      SSet.yonedaEquiv (r ≫ a) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexDiagram_eta F _ _ hb
  have hr : r ≫ (boundary (n + 1)).ι = stdSimplex.map α :=
    (boundary.ι_ι (Fin.last (n + 1))).trans
      (congrArg (fun q ↦ (stdSimplex.map q : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1]))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_eq_lastFace n).symm)
  have hc : stdSimplex.map α ≫ H =
      τ.app (Fin.last n) ≫ (σ ⋙ F).map
        (homOfLE (Fin.le_last (Fin.last n).castSucc)) := by
    rw [← hr, Category.assoc, hH]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient_restriction F σ a (boundary (n + 1)).ι ha r α hr τ
    exact (congrArg SSet.yonedaEquiv.symm hτ).trans (SSet.yonedaEquiv.symm_apply_apply _)
  let ψ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagramSnocOfLastFace (σ ⋙ F) τ H hc
  have ht : ψ.app (Fin.last (n + 1)) = H :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagramSnoc_last (σ ⋙ F) τ H
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagram_lastFace_compatible (σ ⋙ F) τ H hc)
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F α ⟨σ, ψ⟩ = SSet.yonedaEquiv (r ≫ a) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexSnoc_lastFace F σ τ H hc).trans hτ
  refine ⟨ψ, ?_, ht⟩
  apply boundary.hom_ext
  intro j
  rw [← Category.assoc, boundary.ι_ι]
  calc
    _ = SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (SimplexCategory.δ j) ⟨σ, ψ⟩) :=
      SSet.yonedaEquiv_symm_naturality_left (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
        (SimplexCategory.δ j) _
    _ = SSet.yonedaEquiv.symm (SSet.yonedaEquiv (boundary.ι j ≫ a)) := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedBoundary_candidate_face_agreement F σ a ha ψ hp (by rw [ht]; exact hH)]
    _ = _ := SSet.yonedaEquiv.symm_apply_apply _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
