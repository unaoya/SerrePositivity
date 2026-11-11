module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaImagePrismMixed
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.SimplexCoefficientExt
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommaAugPrismSimplex

/-! 恒等 comma への実 dg 関手の像の augmentation prism は、元の全単体 prism に厳密一致。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
  {n : ℕ}

lemma dgGluingCommaImagePrismPhase
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) n) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (p q : Fin 2) (hpq : p ≤ q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismPhaseHom R E E (DGFunctor.id E)
        (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageFunctor R C E F)) β I a b k hI ha hb hk p q hpq =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismPhaseHom R C E F s β I a b k hI ha hb hk p q hpq := by
  fin_cases p <;> fin_cases q
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismPhaseHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageFunctor]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageAugmentationSource_component R C E F _ _ k _
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImagePrismMixed R C E F s I a b k hI ha hb hk β
  · change (1 : ℕ) ≤ 0 at hpq
    omega
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismPhaseHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageFunctor]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageAugmentationTarget_component R C E F _ _ k _

lemma dgGluingCommaImagePrismSimplex
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) n) (β : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E)
        (s.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageFunctor R C E F)) β =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismSimplex R C E F s β := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSimplex_ext_coefficients
  · intro i
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R E E (DGFunctor.id E)) (β i)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageObject R C E F (s.obj i)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R C E F) (β i) (s.obj i)
    have hp : ∀ p : Fin 2, p = 0 ∨ p = 1 := by decide
    rcases hp (β i) with h | h <;> rw [h] <;> rfl
  · intro I a b k hI ha hb hk
    exact heq_of_eq (dgGluingCommaImagePrismPhase R C E F s.toSimplexData β
      I a b k hI ha hb hk (β a) (β b) _)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
