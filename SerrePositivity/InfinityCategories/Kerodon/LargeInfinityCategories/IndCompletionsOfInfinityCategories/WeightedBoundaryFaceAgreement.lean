module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedBoundaryPrefixAgreement

/-!
概要：同じ最後の面と全境界の係数を保つ候補は、元の全境界の各面を保つ。
方針：終点を保つ面の輸送を消去し、残る成分は初区間の比較で決める。
規約：係数の Kan 性は不要。使われ方：weighted 自明 Kan 比較の全境界充填。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Category.{u} I] (F : I ⥤ SSet.{u}) {n : ℕ}
  (σ : ComposableArrows I (n + 1))
  (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
  (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
    (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm σ)
  (ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight (n + 1) ⟶ σ ⋙ F)

/-- 全係数境界を保つ候補の面は、最後の成分でも元の境界面と一致する。 -/
lemma weightedBoundary_candidate_terminal_agreement
    (ht : (boundary (n + 1)).ι ≫ ψ.app (Fin.last (n + 1)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ a (boundary (n + 1)).ι ha)
    (j : Fin (n + 2)) (hjl : j ≠ Fin.last (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (SimplexCategory.δ j) ⟨σ, ψ⟩).2.app (Fin.last n) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedBoundaryFaceDiagram F σ a ha j).app (Fin.last n) := by
  let q := (σ ⋙ F).map
    (homOfLE (Fin.le_last ((SimplexCategory.δ j).toOrderHom (Fin.last n))))
  have : IsIso q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagram_terminal_transport_isIso (σ ⋙ F)
    (SimplexCategory.δ j) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFace_last_of_ne_last j hjl)
  apply (cancel_mono q).1
  calc
    _ = stdSimplex.δ j ≫ ψ.app (Fin.last (n + 1)) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagram_terminal_transport (σ ⋙ F) ψ (SimplexCategory.δ j)
    _ = (boundary.ι j ≫ (boundary (n + 1)).ι) ≫ ψ.app (Fin.last (n + 1)) :=
      congrArg (fun r ↦ r ≫ ψ.app (Fin.last (n + 1))) (boundary.ι_ι j).symm
    _ = boundary.ι j ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ a (boundary (n + 1)).ι ha := by
      rw [Category.assoc, ht]
    _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedBoundaryCoefficient_face F σ a ha j

/-- 同じ最後の面と係数境界を保つ候補は、元の全境界の全ての面を保つ。 -/
lemma weightedBoundary_candidate_face_agreement
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ⟨σ, ψ⟩ =
      SSet.yonedaEquiv (boundary.ι (Fin.last (n + 1)) ≫ a))
    (ht : (boundary (n + 1)).ι ≫ ψ.app (Fin.last (n + 1)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F σ a (boundary (n + 1)).ι ha)
    (j : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (SimplexCategory.δ j) ⟨σ, ψ⟩ =
      SSet.yonedaEquiv (boundary.ι j ≫ a) := by
  by_cases hjl : j = Fin.last (n + 1)
  · subst j
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_eq_lastFace]
    exact hp
  · calc
      _ = ⟨(SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ,
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedBoundaryFaceDiagram F σ a ha j⟩ := by
        refine Sigma.ext (by rfl) ?_
        apply heq_of_eq
        apply NatTrans.ext
        funext i
        by_cases hi : (SimplexCategory.δ j).toOrderHom i = Fin.last (n + 1)
        · have hie := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFace_eq_last_of_image_last j i hi
          subst i
          exact weightedBoundary_candidate_terminal_agreement F σ a ha ψ ht j hjl
        · have hlt := Fin.lt_last_iff_ne_last.mpr hi
          have hib := Nat.le_of_lt_succ hlt
          exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedBoundary_candidate_prefix_agreement F σ a ha ψ hp j i hib
      _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedBoundaryFaceDiagram_eta F σ a ha j

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
