module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.AugmentationProofCases
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationCollapsedPair
/-!
概要：同じ実 augmentation 候補と実単体の族が、全単調添字変更と厳密に可換と示す。
方針：添字集合上単射・非単射高次・潰れた二点の三つの実係数比較を結合する。
規約：全単体作用を実際に検証する。使われ方：実 nerve prism 写像の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
/-- 同じ実候補の全正しい係数は、任意の単調添字変更と可換。 -/
lemma dgModuleAugmentationPrismData_hom_pullback
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F (s.pullback α) (β.comp α)).hom
        I a b k hI ha hb hk =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F s β).pullback α).hom I a b k hI ha hb hk := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.augmentation_proof_of_reindex_cases α I
    (fun hi ↦ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData_hom_pullback_of_inj R C E F s α β I a b k
      hI ha hb hk hi)
    (fun hi hc ↦ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData_hom_pullback_of_collapsed_pair R C E F s α β
      I a b k hI ha hb hk hi hc)
    (fun hi hc ↦ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData_hom_pullback_of_not_inj R C E F s α β I a b k
      hI ha hb hk hi hc)
/-- 元の同じ実 augmentation データは、任意の単調添字変更と厳密に可換。 -/
lemma dgModuleAugmentationPrismData_pullback
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F (s.pullback α) (β.comp α) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismData R C E F s β).pullback α := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    exact dgModuleAugmentationPrismData_hom_pullback R C E F s α β I a b k hI ha hb hk
/-- 実 augmentation 単体の族は、すべての面・退化を含む全添字作用と厳密に可換。 -/
lemma dgModuleAugmentationPrismSimplex_pullback
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismSimplex R C E F (s.pullback α) (β.comp α) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismSimplex R C E F s β).pullback α := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact dgModuleAugmentationPrismData_pullback R C E F s.toSimplexData α β
end SerrePositivity.InfinityCategories.Project.DerivedCategories
