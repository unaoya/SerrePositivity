module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationPrecompCuts
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (A C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A C) (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R A E (H.comp F)) n)
  (β : Fin (n + 1) →o Fin 2)
  (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
  (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
  (hk : k = 2 - (I.card : ℤ))
/-- 四つの相の組ごとに、同じ全斉次係数が入力前合成で保たれる。 -/
lemma dgModuleAugmentationPrismPhaseHom_precomp (p q : Fin 2) (hpq : p ≤ q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismPhaseHom R C E F
      (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R A C E H F)) β I a b k hI ha hb hk p q hpq =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismPhaseHom R A E (H.comp F) s β I a b k hI ha hb hk p q hpq := by
  fin_cases p <;> fin_cases q
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismPhaseHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.map,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource_hom_precomp R A C E H F (s.obj a) (s.obj b) _ _
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismMixedHom_precomp R A C E H F s β I a b k hI ha hb hk
  · simp at hpq
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismPhaseHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.map,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget_hom_precomp R A C E H F (s.obj a) (s.obj b) _ _
/-- 実全 simplex data は、同じ入力 dg 関手の前合成と厳密に可換。 -/
lemma dgModuleAugmentationPrismData_precomp :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F
      (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R A C E H F)) β =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R A E (H.comp F) s β := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    exact dgModuleAugmentationPrismPhaseHom_precomp R A C E H F s β I a b k hI ha hb hk _ _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
