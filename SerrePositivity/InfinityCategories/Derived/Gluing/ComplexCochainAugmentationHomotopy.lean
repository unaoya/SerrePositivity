module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainAugmentationHomotopy
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedUnitModel

/-! 任意複体の比較 cochain を、元 augmentation prism からの同じ実 pinched ホモトピーへ送る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory
open scoped Simplicial
variable {R : Type u} [CommRing R] {K L : Complex R}
  (f g : K ⟶ L) (h : Cochain K L (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))

include he in
lemma dgGluingCochainUnitHom_boundary :
    δ (-1) 0 (h.comp (Cochain.ofHom (complexUnitHomIso L).hom) (add_zero (-1))) =
      Cochain.ofHom (g ≫ (complexUnitHomIso L).hom - f ≫ (complexUnitHomIso L).hom) := by
  rw [δ_comp_ofHom, he, ← Cochain.ofHom_comp, Preadditive.sub_comp]

def dgGluingComplexCochainAugmentationPrism :
    (Δ[1] : SSet.{max u v}) ⊗ complexPinchedSpace.{u, max u v} K ⟶
      complexPinchedSpace.{u, max u v} L :=
  dgGluingCochainAugmentationPrism R (DGComplexPinchedModel.{u, max u v} L)
    (complexPinchedSource L) (complexPinchedTarget L) K
    (f ≫ (complexUnitHomIso L).hom) (g ≫ (complexUnitHomIso L).hom)
    (h.comp (Cochain.ofHom (complexUnitHomIso L).hom) (add_zero (-1)))
    (dgGluingCochainUnitHom_boundary f g h he)

lemma dgGluingComplexCochainAugmentationPrism_zero :
    prismEndpoint 0 _ ≫ dgGluingComplexCochainAugmentationPrism.{u, v} f g h he =
      complexPinchedMap.{u, max u v} f := by
  rw [dgGluingComplexCochainAugmentationPrism, dgGluingCochainAugmentationPrism_zero,
    dgGluingComplexPinchedUnitHom_cancel]

lemma dgGluingComplexCochainAugmentationPrism_one :
    prismEndpoint 1 _ ≫ dgGluingComplexCochainAugmentationPrism.{u, v} f g h he =
      complexPinchedMap.{u, max u v} g := by
  rw [dgGluingComplexCochainAugmentationPrism, dgGluingCochainAugmentationPrism_one,
    dgGluingComplexPinchedUnitHom_cancel]

def dgGluingComplexCochainAugmentationHomotopy :
    SSet.Homotopy (complexPinchedMap.{u, max u v} f) (complexPinchedMap.{u, max u v} g) :=
  dgGluingHomotopyOfPrism (dgGluingComplexCochainAugmentationPrism f g h he)
    (dgGluingComplexCochainAugmentationPrism_zero f g h he)
    (dgGluingComplexCochainAugmentationPrism_one f g h he)

lemma dgGluingComplexCochainAugmentationHomotopy_h :
    (dgGluingComplexCochainAugmentationHomotopy.{u, v} f g h he).h =
      (β_ (complexPinchedSpace.{u, max u v} K) (Δ[1] : SSet.{max u v})).hom ≫
        dgGluingComplexCochainAugmentationPrism f g h he := rfl

end SerrePositivity.InfinityCategories
