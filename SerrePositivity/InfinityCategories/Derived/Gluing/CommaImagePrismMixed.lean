module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaImageAugmentationComponents

/-! 恒等 comma への実 dg 関手で、元 augmentation prism の全切断補正と混合係数を保つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  {n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) n)
  (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
  (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
  (hk : k = 2 - (I.card : ℤ))

lemma dgGluingCommaImagePrismCut (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    dgCommaAugmentationPrismCut R E E (DGFunctor.id E)
        (s.map (dgGluingCommaImageFunctor R C E F)) I a b k hI ha hb hk j hj haj hjb =
      dgCommaAugmentationPrismCut R C E F s I a b k hI ha hb hk j hj haj hjb := by
  dsimp only [dgCommaAugmentationPrismCut, SimplexData.map, dgGluingCommaImageFunctor]
  apply congrArg (fun z : GradedHom R (s.obj a).replacement (F.obj (s.obj b).source) k =>
    ((I.filter (j < ·)).card : ℤ).negOnePow • z)
  apply congrArg₂ (fun
    (v : GradedHom R (s.obj j).replacement (F.obj (s.obj b).source)
      (2 - ((I.filter (j ≤ ·)).card : ℤ) - 1))
    (w : GradedHom R (s.obj a).replacement (s.obj j).replacement
      (2 - ((I.filter (· ≤ j)).card : ℤ))) =>
      compose R v w (by have := Index.split_card hj; omega))
  · exact dgGluingCommaImageAugmentationHomotopy_component R C E F _ _ _ _
  · exact dgGluingCommaImageAugmentationSource_component R C E F _ _ _ _

lemma dgGluingCommaImagePrismMixed (β : Fin (n + 1) →o Fin 2) :
    dgCommaAugmentationPrismMixedHom R E E (DGFunctor.id E)
        (s.map (dgGluingCommaImageFunctor R C E F)) β I a b k hI ha hb hk =
      dgCommaAugmentationPrismMixedHom R C E F s β I a b k hI ha hb hk := by
  dsimp only [dgCommaAugmentationPrismMixedHom]
  simp only [dgGluingCommaImagePrismCut R C E F s I a b k hI ha hb hk]
  dsimp only [SimplexData.map, dgGluingCommaImageFunctor]
  apply congrArg (fun z : GradedHom R (s.obj a).replacement (F.obj (s.obj b).source) k =>
    z + ∑ j : I, if h : a < j.val ∧ j.val < b ∧ β j.val = 1 then
      dgCommaAugmentationPrismCut R C E F s I a b k hI ha hb hk j.val j.property h.1 h.2.1
      else 0)
  apply congrArg₂ (fun
    (v : GradedHom R (s.obj b).replacement (F.obj (s.obj b).source) 0)
    (w : GradedHom R (s.obj a).replacement (s.obj b).replacement k) =>
      compose R v w (add_zero k))
  · exact dgGluingCommaImageAugmentationComponent R C E F _
  · exact dgGluingCommaImageAugmentationSource_component R C E F _ _ _ _

end SerrePositivity.InfinityCategories
