module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Augmentations.ComplexAugmentationPost

/-! Hom 複体の実同型で移した明示 cochain prism は、同じ元複体の明示 prism へ全時間で戻る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (E : Type (max u v)) [DGCategory R E]
  (x y : E) {K L : Complex R} (e : homObject R E x y ≅ L)
  (f g : K ⟶ L) (h : Cochain K L (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))

lemma dgGluingCochainAugmentationPrism_iso_target :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism R E x y K (f ≫ e.inv) (g ≫ e.inv)
        (h.comp (Cochain.ofHom e.inv) (add_zero (-1)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainPost_boundary f g h he e.inv) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := E) (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u v} L)
        (x := x) (y := y) (x' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource L) (y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget L)
        (e.hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainAugmentationPrism.{u, v} f g h he := by
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism_post R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u v} L)
    x y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource L) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget L) K (f ≫ e.inv) (g ≫ e.inv)
    (h.comp (Cochain.ofHom e.inv) (add_zero (-1)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainPost_boundary f g h he e.inv) (e.hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom)
  refine ht.trans ?_
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainAugmentationPrism
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism_congr
  · simp only [Category.assoc, e.inv_hom_id_assoc]
  · simp only [Category.assoc, e.inv_hom_id_assoc]
  · rw [Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, e.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
