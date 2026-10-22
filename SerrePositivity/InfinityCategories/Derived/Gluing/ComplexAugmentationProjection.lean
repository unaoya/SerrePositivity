module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainAugmentationProjection
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexCochainAugmentationHomotopy

/-! 任意複体での明示 cochain prism は、cochain を消す実鎖射影の下で定値。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory
open CartesianMonoidalCategory
open scoped Simplicial
variable {R : Type u} [CommRing R] {K L Q : Complex R}
  (f g : K ⟶ L) (h : Cochain K L (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))
  (q : L ⟶ Q) (hp : g ≫ q = f ≫ q)
  (hz : h.comp (Cochain.ofHom q) (add_zero (-1)) = 0)

include hp hz in
lemma dgGluingComplexCochainAugmentationPrism_post_zero :
    dgGluingComplexCochainAugmentationPrism.{u, v} f g h he ≫
        complexPinchedMap.{u, max u v} q =
      snd Δ[1] (complexPinchedSpace.{u, max u v} K) ≫ complexPinchedMap.{u, max u v} (f ≫ q) := by
  have hη : (complexUnitHomIso L).hom ≫ homPostcompose (𝟙_ (Complex R)) q =
      q ≫ (complexUnitHomIso Q).hom := complexUnitHomIso_naturality q
  have hp' : (g ≫ (complexUnitHomIso L).hom) ≫ homPostcompose (𝟙_ (Complex R)) q =
      (f ≫ (complexUnitHomIso L).hom) ≫ homPostcompose (𝟙_ (Complex R)) q := by
    calc
      _ = g ≫ q ≫ (complexUnitHomIso Q).hom := by rw [Category.assoc, hη]
      _ = f ≫ q ≫ (complexUnitHomIso Q).hom := by rw [← Category.assoc, hp, Category.assoc]
      _ = _ := by rw [Category.assoc, hη]
  have hz' : (h.comp (Cochain.ofHom (complexUnitHomIso L).hom) (add_zero (-1))).comp
      (Cochain.ofHom (homPostcompose (𝟙_ (Complex R)) q)) (add_zero (-1)) = 0 := by
    rw [Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, hη,
      Cochain.ofHom_comp, ← Cochain.comp_assoc_of_third_is_zero_cochain, hz, Cochain.zero_comp]
  have ht := dgGluingCochainAugmentationPrism_post_zero R (DGComplexPinchedModel.{u, max u v} L)
    (complexPinchedSource L) (complexPinchedTarget L) K
    (f ≫ (complexUnitHomIso L).hom) (g ≫ (complexUnitHomIso L).hom)
    (h.comp (Cochain.ofHom (complexUnitHomIso L).hom) (add_zero (-1)))
    (dgGluingCochainUnitHom_boundary f g h he)
    (T := DGComplexPinchedModel.{u, max u v} Q)
    (x' := complexPinchedSource Q) (y' := complexPinchedTarget Q)
    (homPostcompose (𝟙_ (Complex R)) q) hp' hz'
  change dgGluingCochainAugmentationPrism _ _ _ _ _ _ _ _ _ ≫ _ = _
  refine ht.trans ?_
  rw [Category.assoc f, hη, ← Category.assoc f q, dgGluingComplexPinchedUnitHom_cancel]

end SerrePositivity.InfinityCategories
