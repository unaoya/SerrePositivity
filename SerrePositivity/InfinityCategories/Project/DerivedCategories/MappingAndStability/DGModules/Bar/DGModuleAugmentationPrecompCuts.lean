module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationPrecompCoordinates
/-!
概要：実 augmentation prism の内部切断項と混合係数は入力前合成を保つ。
方針：比較 cochain と両射影の全次数保存を、同じ補正項と有限和へ移す。
規約：切断添字・符号・係数を変更しない。使われ方：全 prism の入力自然性。
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
/-- 同じ各内部切断の補正項は、入力前合成で厳密に保たれる。 -/
lemma dgModuleAugmentationPrismCut_precomp (j : Fin (n + 1)) (hj : j ∈ I)
    (haj : a < j) (hjb : j < b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismCut R C E F
      (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R A C E H F)) I a b k hI ha hb hk j hj haj hjb =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismCut R A E (H.comp F) s I a b k hI ha hb hk j hj haj hjb := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismCut, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor]
  congr 2
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyComponent_precomp R A C E H F (s.obj j) (s.obj b) _ _
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource_hom_precomp R A C E H F (s.obj a) (s.obj j) _ _
/-- 同じ実切断補正和からなる混合係数は、入力前合成で厳密に保たれる。 -/
lemma dgModuleAugmentationPrismMixedHom_precomp :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismMixedHom R C E F
      (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R A C E H F)) β I a b k hI ha hb hk =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismMixedHom R A E (H.comp F) s β I a b k hI ha hb hk := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismMixedHom
  apply congrArg₂ (· + ·)
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor]
    congr 1
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource_hom_precomp R A C E H F (s.obj a) (s.obj b) _ _
  · apply Finset.sum_congr rfl
    intro j hj
    split_ifs with h
    · exact dgModuleAugmentationPrismCut_precomp R A C E H F s I a b k hI ha hb hk
        j.val j.property h.1 h.2.1
    · rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
