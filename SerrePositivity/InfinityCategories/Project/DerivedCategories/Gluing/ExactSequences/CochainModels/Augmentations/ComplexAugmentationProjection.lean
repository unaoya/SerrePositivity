module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Augmentations.CochainAugmentationProjection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.ComplexCochainAugmentationHomotopy

/-! 任意複体での明示 cochain prism は、cochain を消す実鎖射影の下で定値。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory
open CartesianMonoidalCategory
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {K L Q : Complex R}
  (f g : K ⟶ L) (h : Cochain K L (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))
  (q : L ⟶ Q) (hp : g ≫ q = f ≫ q)
  (hz : h.comp (Cochain.ofHom q) (add_zero (-1)) = 0)

include hp hz in
lemma dgGluingComplexCochainAugmentationPrism_post_zero :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexCochainAugmentationPrism.{u, v} f g h he ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v} q =
      snd Δ[1] (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v} K) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v} (f ≫ q) := by
  have hη : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom ≫ homPostcompose (𝟙_ (Complex R)) q =
      q ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso Q).hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso_naturality q
  have hp' : (g ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) ≫ homPostcompose (𝟙_ (Complex R)) q =
      (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) ≫ homPostcompose (𝟙_ (Complex R)) q := by
    calc
      _ = g ≫ q ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso Q).hom := by rw [Category.assoc, hη]
      _ = f ≫ q ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso Q).hom := by rw [← Category.assoc, hp, Category.assoc]
      _ = _ := by rw [Category.assoc, hη]
  have hz' : (h.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) (add_zero (-1))).comp
      (Cochain.ofHom (homPostcompose (𝟙_ (Complex R)) q)) (add_zero (-1)) = 0 := by
    rw [Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, hη,
      Cochain.ofHom_comp, ← Cochain.comp_assoc_of_third_is_zero_cochain, hz, Cochain.zero_comp]
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism_post_zero R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u v} L)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource L) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget L) K
    (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) (g ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom)
    (h.comp (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso L).hom) (add_zero (-1)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainUnitHom_boundary f g h he)
    (T := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u v} Q)
    (x' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource Q) (y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget Q)
    (homPostcompose (𝟙_ (Complex R)) q) hp' hz'
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism _ _ _ _ _ _ _ _ _ ≫ _ = _
  refine ht.trans ?_
  rw [Category.assoc f, hη, ← Category.assoc f q, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedUnitHom_cancel]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
