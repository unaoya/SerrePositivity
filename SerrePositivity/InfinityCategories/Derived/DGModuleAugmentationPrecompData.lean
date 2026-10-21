module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationPrecompCuts
/-!
概要：同じ実 augmentation の全対象・全斉次係数は入力前合成を保つ。
方針：相ごとに両射影と混合係数の厳密な保存を使い、全データを比較する。
規約：全次元・全切断を扱う。使われ方：実 prism 単体と円柱写像の入力自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (A C : Type v) [DGCategory R A] [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  (H : DGFunctor R A C) (F : DGFunctor R C (RightModule R E))
  {n : ℕ} (s : SimplexData R (DGModuleFunctorResolutionObject R A E (H.comp F)) n)
  (β : Fin (n + 1) →o Fin 2)
  (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
  (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
  (hk : k = 2 - (I.card : ℤ))
/-- 四つの相の組ごとに、同じ全斉次係数が入力前合成で保たれる。 -/
lemma dgModuleAugmentationPrismPhaseHom_precomp (p q : Fin 2) (hpq : p ≤ q) :
    dgModuleAugmentationPrismPhaseHom R C E F
      (s.map (dgModuleResolutionPrecompFunctor R A C E H F)) β I a b k hI ha hb hk p q hpq =
    dgModuleAugmentationPrismPhaseHom R A E (H.comp F) s β I a b k hI ha hb hk p q hpq := by
  fin_cases p <;> fin_cases q
  · dsimp only [dgModuleAugmentationPrismPhaseHom, SimplexData.map,
      dgModuleResolutionPrecompFunctor]
    exact dgModuleAugmentationSource_hom_precomp R A C E H F (s.obj a) (s.obj b) _ _
  · exact dgModuleAugmentationPrismMixedHom_precomp R A C E H F s β I a b k hI ha hb hk
  · simp at hpq
  · dsimp only [dgModuleAugmentationPrismPhaseHom, SimplexData.map,
      dgModuleResolutionPrecompFunctor]
    exact dgModuleAugmentationTarget_hom_precomp R A C E H F (s.obj a) (s.obj b) _ _
/-- 実全 simplex data は、同じ入力 dg 関手の前合成と厳密に可換。 -/
lemma dgModuleAugmentationPrismData_precomp :
    dgModuleAugmentationPrismData R C E F
      (s.map (dgModuleResolutionPrecompFunctor R A C E H F)) β =
    dgModuleAugmentationPrismData R A E (H.comp F) s β := by
  apply SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    exact dgModuleAugmentationPrismPhaseHom_precomp R A C E H F s β I a b k hI ha hb hk _ _ _
end SerrePositivity.InfinityCategories
