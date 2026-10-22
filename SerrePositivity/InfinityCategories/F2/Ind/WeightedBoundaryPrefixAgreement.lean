module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedBoundaryDiagrams

/-!
概要：最後の面を保つ weighted 境界の候補は、他の面の終点を避ける全成分を保つ。
方針：初区間を最後の面へ因子分解し、同じ境界内の交わりを比較する。
規約：係数の充填性は不要。使われ方：weighted nerve の全境界の充填検査。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 最後の面との一致は、全ての他の面の初区間での一致を強制する。 -/
lemma weightedBoundary_candidate_prefix_agreement {I : Type u} [Category.{u} I]
    (F : I ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows I (n + 1))
    (a : (boundary (n + 1) : SSet.{u}) ⟶ weightedNerve F)
    (ha : a ≫ weightedNerveProjection F =
      (boundary (n + 1)).ι ≫ SSet.yonedaEquiv.symm σ)
    (ψ : simplexPrefixWeight (n + 1) ⟶ σ ⋙ F)
    (hp : weightedNerveSimplexMap F
        (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ⟨σ, ψ⟩ =
      SSet.yonedaEquiv (boundary.ι (Fin.last (n + 1)) ≫ a))
    (j : Fin (n + 2)) (i : Fin (n + 1))
    (hi : ((SimplexCategory.δ j).toOrderHom i).val ≤ n) :
    (weightedNerveSimplexMap F (SimplexCategory.δ j) ⟨σ, ψ⟩).2.app i =
      (weightedBoundaryFaceDiagram F σ a ha j).app i := by
  let β := simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)
  let γ := simplexPrefixThroughLast (SimplexCategory.δ j) i hi
  let s : weightedNerveSimplex F (n + 1) := ⟨σ, ψ⟩
  have hr : (stdSimplex.map β : (Δ[i.val] : SSet.{u}) ⟶ Δ[n]) ≫ boundary.ι j =
      stdSimplex.map γ ≫ boundary.ι (Fin.last (n + 1)) := by
    apply (cancel_mono (boundary (n + 1)).ι).1
    simp only [Category.assoc, boundary.ι_ι]
    change stdSimplex.map β ≫ stdSimplex.map (SimplexCategory.δ j) =
      stdSimplex.map γ ≫ stdSimplex.map (SimplexCategory.δ (Fin.last (n + 1)))
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    rw [← simplexPrefixInclusion_eq_lastFace]
    exact congrArg (fun q ↦ (stdSimplex.map q :
      (Δ[i.val] : SSet.{u}) ⟶ Δ[n + 1]))
      (simplexPrefixThroughLast_factor (SimplexCategory.δ j) i hi).symm
  have hov : weightedNerveSimplexMap F β (SSet.yonedaEquiv (boundary.ι j ≫ a)) =
      weightedNerveSimplexMap F γ
        (SSet.yonedaEquiv (boundary.ι (Fin.last (n + 1)) ≫ a)) := by
    change (weightedNerve F).map β.op _ = (weightedNerve F).map γ.op _
    rw [SSet.yonedaEquiv_naturality, SSet.yonedaEquiv_naturality]
    apply congrArg SSet.yonedaEquiv
    rw [← Category.assoc, ← Category.assoc, hr]
  have he : weightedNerveSimplexMap F β (weightedNerveSimplexMap F (SimplexCategory.δ j) s) =
      weightedNerveSimplexMap F β
        ⟨(SimplexCategory.toCat.map (SimplexCategory.δ j)).toFunctor ⋙ σ,
          weightedBoundaryFaceDiagram F σ a ha j⟩ := by
    calc
      _ = weightedNerveSimplexMap F (β ≫ SimplexCategory.δ j) s :=
        weightedNerveSimplexMap_comp F β (SimplexCategory.δ j) s
      _ = weightedNerveSimplexMap F
          (γ ≫ simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) s :=
        congrArg (fun q ↦ weightedNerveSimplexMap F q s)
          (simplexPrefixThroughLast_factor (SimplexCategory.δ j) i hi).symm
      _ = weightedNerveSimplexMap F γ (weightedNerveSimplexMap F
          (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) s) :=
        (weightedNerveSimplexMap_comp F γ _ s).symm
      _ = weightedNerveSimplexMap F γ
          (SSet.yonedaEquiv (boundary.ι (Fin.last (n + 1)) ≫ a)) :=
        congrArg (weightedNerveSimplexMap F γ) hp
      _ = _ := by rw [weightedBoundaryFaceDiagram_eta]; exact hov.symm
  have ht := weightedNerveSimplex_last_heq F he
  change HEq
    (stdSimplex.map (simplexPrefixRestriction β (Fin.last i.val)) ≫
      (weightedNerveSimplexMap F (SimplexCategory.δ j) ⟨σ, ψ⟩).2.app i)
    (stdSimplex.map (simplexPrefixRestriction β (Fin.last i.val)) ≫
      (weightedBoundaryFaceDiagram F σ a ha j).app i) at ht
  dsimp only [β] at ht
  rw [simplexPrefixRestriction_inclusion, CategoryTheory.Functor.map_id,
    Category.id_comp] at ht
  exact eq_of_heq ht

end SerrePositivity.InfinityCategories.F2.Ind
