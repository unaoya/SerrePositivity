module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Augmentations.CochainAugmentationPost
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Augmentations.CochainAugmentationCongr
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.ComplexCochainAugmentationHomotopy

/-! 任意複体の明示的な全 augmentation prism は、任意の実鎖写像による後合成に自然。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory
variable {R : Type u} [CommRing R] {K L Q : Complex R}
  (f g : K ⟶ L) (h : Cochain K L (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))
  (q : L ⟶ Q)

lemma dgGluingComplexCochainAugmentationPrism_post :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainAugmentationPrism.{u, v} f g h he ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v} q =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainAugmentationPrism.{u, v} (f ≫ q) (g ≫ q)
        (h.comp (Cochain.ofHom q) (add_zero (-1))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainPost_boundary f g h he q) := by
  have hη : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom ≫ homPostcompose (𝟙_ (Complex R)) q =
      q ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso Q).hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso_naturality q
  have hh : (h.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) (add_zero (-1))).comp
      (Cochain.ofHom (homPostcompose (𝟙_ (Complex R)) q)) (add_zero (-1)) =
      (h.comp (Cochain.ofHom q) (add_zero (-1))).comp
        (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso Q).hom) (add_zero (-1)) := by
    rw [Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, hη,
      Cochain.ofHom_comp, ← Cochain.comp_assoc_of_third_is_zero_cochain]
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism_post R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u v} L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u v} Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource L) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource Q) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget Q)
    K (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) (g ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom)
    (h.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) (add_zero (-1)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainUnitHom_boundary f g h he) (homPostcompose (𝟙_ (Complex R)) q)
  refine ht.trans ?_
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainAugmentationPrism
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism_congr
  · rw [Category.assoc, hη, Category.assoc]
  · rw [Category.assoc, hη, Category.assoc]
  · exact hh

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
