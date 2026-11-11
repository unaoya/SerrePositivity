module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedBoundaryDiagrams

/-!
概要：最後の面を保つ weighted 境界の候補は、他の面の終点を避ける全成分を保つ。
方針：初区間を最後の面へ因子分解し、同じ境界内の交わりを比較する。
規約：係数の充填性は不要。使われ方：weighted nerve の全境界の充填検査。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 最後の面との一致は、全ての他の面の初区間での一致を強制する。 -/
lemma weightedBoundary_candidate_prefix_agreement {I : Type u} [Category.{u} I]
    (F : I ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows I (n + 1))
    (a : (boundary (n + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
      (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm σ)
    (ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight (n + 1) ⟶ σ ⋙ F)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ⟨σ, ψ⟩ =
      SSet.yonedaEquiv (boundary.ι (Fin.last (n + 1)) ≫ a))
    (j : Fin (n + 2)) (i : Fin (n + 1))
    (hi : ((SimplexCategory.δ j).toOrderHom i).val ≤ n) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (SimplexCategory.δ j) ⟨σ, ψ⟩).2.app i =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedBoundaryFaceDiagram F σ a ha j).app i := by
  let β := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)
  let γ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixThroughLast (SimplexCategory.δ j) i hi
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F (n + 1) := ⟨σ, ψ⟩
  have hr : (stdSimplex.map β : (Δ[i.val] : SSet.{u}) ⟶ Δ[n]) ≫ boundary.ι j =
      stdSimplex.map γ ≫ boundary.ι (Fin.last (n + 1)) := by
    apply (cancel_mono (boundary (n + 1)).ι).1
    simp only [Category.assoc, boundary.ι_ι]
    change stdSimplex.map β ≫ stdSimplex.map (SimplexCategory.δ j) =
      stdSimplex.map γ ≫ stdSimplex.map (SimplexCategory.δ (Fin.last (n + 1)))
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_eq_lastFace]
    exact congrArg (fun q ↦ (stdSimplex.map q :
      (Δ[i.val] : SSet.{u}) ⟶ Δ[n + 1]))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixThroughLast_factor (SimplexCategory.δ j) i hi).symm
  have hov : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F β (SSet.yonedaEquiv (boundary.ι j ≫ a)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F γ
        (SSet.yonedaEquiv (boundary.ι (Fin.last (n + 1)) ≫ a)) := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F).map β.op _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F).map γ.op _
    rw [SSet.yonedaEquiv_naturality, SSet.yonedaEquiv_naturality]
    apply congrArg SSet.yonedaEquiv
    rw [← Category.assoc, ← Category.assoc, hr]
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F β (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (SimplexCategory.δ j) s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F β
        ⟨(SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ,
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedBoundaryFaceDiagram F σ a ha j⟩ := by
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (β ≫ SimplexCategory.δ j) s :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap_comp F β (SimplexCategory.δ j) s
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F
          (γ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) s :=
        congrArg (fun q ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F q s)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixThroughLast_factor (SimplexCategory.δ j) i hi).symm
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F γ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) s) :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap_comp F γ _ s).symm
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F γ
          (SSet.yonedaEquiv (boundary.ι (Fin.last (n + 1)) ≫ a)) :=
        congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F γ) hp
      _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedBoundaryFaceDiagram_eta]; exact hov.symm
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex_last_heq F he
  change HEq
    (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction β (Fin.last i.val)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (SimplexCategory.δ j) ⟨σ, ψ⟩).2.app i)
    (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction β (Fin.last i.val)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedBoundaryFaceDiagram F σ a ha j).app i) at ht
  dsimp only [β] at ht
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction_inclusion, CategoryTheory.Functor.map_id,
    Category.id_comp] at ht
  exact eq_of_heq ht

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
