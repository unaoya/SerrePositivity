module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaImagePrismMixed
public import SerrePositivity.InfinityCategories.Derived.Gluing.SimplexCoefficientExt
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugPrismSimplex

/-! 恒等 comma への実 dg 関手の像の augmentation prism は、元の全単体 prism に厳密一致。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  {n : ℕ}

lemma dgGluingCommaImagePrismPhase
    (s : SimplexData R (DGFunctorCommaObject R C E F) n) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (p q : Fin 2) (hpq : p ≤ q) :
    dgCommaAugmentationPrismPhaseHom R E E (DGFunctor.id E)
        (s.map (dgGluingCommaImageFunctor R C E F)) β I a b k hI ha hb hk p q hpq =
      dgCommaAugmentationPrismPhaseHom R C E F s β I a b k hI ha hb hk p q hpq := by
  fin_cases p <;> fin_cases q
  · dsimp only [dgCommaAugmentationPrismPhaseHom, SimplexData.map, dgGluingCommaImageFunctor]
    exact dgGluingCommaImageAugmentationSource_component R C E F _ _ k _
  · exact dgGluingCommaImagePrismMixed R C E F s I a b k hI ha hb hk β
  · change (1 : ℕ) ≤ 0 at hpq
    omega
  · dsimp only [dgCommaAugmentationPrismPhaseHom, SimplexData.map, dgGluingCommaImageFunctor]
    exact dgGluingCommaImageAugmentationTarget_component R C E F _ _ k _

lemma dgGluingCommaImagePrismSimplex
    (s : Simplex R (DGFunctorCommaObject R C E F) n) (β : Fin (n + 1) →o Fin 2) :
    dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
        (s.map (dgGluingCommaImageFunctor R C E F)) β =
      dgCommaAugmentationPrismSimplex R C E F s β := by
  apply dgGluingSimplex_ext_coefficients
  · intro i
    change StrictNatTrans.phaseObj (dgCommaAugmentationSource R E E (DGFunctor.id E))
        (dgCommaAugmentationTarget R E E (DGFunctor.id E)) (β i)
        (dgGluingCommaImageObject R C E F (s.obj i)) =
      StrictNatTrans.phaseObj (dgCommaAugmentationSource R C E F)
        (dgCommaAugmentationTarget R C E F) (β i) (s.obj i)
    have hp : ∀ p : Fin 2, p = 0 ∨ p = 1 := by decide
    rcases hp (β i) with h | h <;> rw [h] <;> rfl
  · intro I a b k hI ha hb hk
    exact heq_of_eq (dgGluingCommaImagePrismPhase R C E F s.toSimplexData β
      I a b k hI ha hb hk (β a) (β b) _)

end SerrePositivity.InfinityCategories
