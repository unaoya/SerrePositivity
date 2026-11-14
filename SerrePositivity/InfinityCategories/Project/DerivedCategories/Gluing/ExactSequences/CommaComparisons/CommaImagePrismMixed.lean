module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CommaComparisons.CommaImageAugmentationComponents

/-! 恒等 comma への実 dg 関手で、元 augmentation prism の全切断補正と混合係数を保つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) n)
  (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
  (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
  (hk : k = 2 - (I.card : ℤ))

lemma dgGluingCommaImagePrismCut (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismCut R E E (DGFunctor.id E)
        (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageFunctor R C E F)) I a b k hI ha hb hk j hj haj hjb =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismCut R C E F s I a b k hI ha hb hk j hj haj hjb := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismCut, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageFunctor]
  apply congrArg (fun z : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a).replacement (F.obj (s.obj b).source) k =>
    ((I.filter (j < ·)).card : ℤ).negOnePow • z)
  apply congrArg₂ (fun
    (v : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj j).replacement (F.obj (s.obj b).source)
      (2 - ((I.filter (j ≤ ·)).card : ℤ) - 1))
    (w : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a).replacement (s.obj j).replacement
      (2 - ((I.filter (· ≤ j)).card : ℤ))) =>
      compose R v w (by have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj; omega))
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageAugmentationHomotopy_component R C E F _ _ _ _
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageAugmentationSource_component R C E F _ _ _ _

lemma dgGluingCommaImagePrismMixed (β : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom R E E (DGFunctor.id E)
        (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageFunctor R C E F)) β I a b k hI ha hb hk =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom R C E F s β I a b k hI ha hb hk := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismMixedHom]
  simp only [dgGluingCommaImagePrismCut R C E F s I a b k hI ha hb hk]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageFunctor]
  apply congrArg (fun z : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a).replacement (F.obj (s.obj b).source) k =>
    z + ∑ j : I, if h : a < j.val ∧ j.val < b ∧ β j.val = 1 then
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismCut R C E F s I a b k hI ha hb hk j.val j.property h.1 h.2.1
      else 0)
  apply congrArg₂ (fun
    (v : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj b).replacement (F.obj (s.obj b).source) 0)
    (w : _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a).replacement (s.obj b).replacement k) =>
      _root_.SerrePositivity.DifferentialGraded.compose R v w (add_zero k))
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageAugmentationComponent R C E F _
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageAugmentationSource_component R C E F _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
