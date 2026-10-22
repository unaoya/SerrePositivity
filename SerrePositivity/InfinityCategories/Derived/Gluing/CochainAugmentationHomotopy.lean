module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainIdentityCommaPinchedInput
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPinchedHomotopy

/-! 元の augmentation prism 自身から作る、任意の比較 cochain の全 pinched Hom ホモトピー。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) [DGCategory R E] (x y : E)
  (K : Complex R) (f g : K ⟶ homObject R E x y)
  (h : Cochain K (homObject R E x y) (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))

def dgGluingCochainAugmentationPrism :
    (Δ[1] : SSet.{max u v}) ⊗ complexPinchedSpace.{u, max u v} K ⟶
      DGNerve.pinchedHom R E x y :=
  ((Δ[1] : SSet.{max u v}) ◁
    dgGluingCochainIdentityCommaPinchedInput R E x y K f g h he) ≫
      dgGluingIdentityCommaPinchedPrism R E x y

lemma dgGluingCochainAugmentationPrism_zero :
    prismEndpoint 0 _ ≫ dgGluingCochainAugmentationPrism R E x y K f g h he =
      complexPinchedMap.{u, max u v} f ≫ (pinchedComplexModelIso x y).inv := by
  rw [dgGluingCochainAugmentationPrism, ← Category.assoc, prismEndpoint_naturality,
    Category.assoc, dgGluingIdentityCommaPinchedPrism_zero,
    dgGluingCochainIdentityCommaPinchedInput_start]

lemma dgGluingCochainAugmentationPrism_one :
    prismEndpoint 1 _ ≫ dgGluingCochainAugmentationPrism R E x y K f g h he =
      complexPinchedMap.{u, max u v} g ≫ (pinchedComplexModelIso x y).inv := by
  rw [dgGluingCochainAugmentationPrism, ← Category.assoc, prismEndpoint_naturality,
    Category.assoc, dgGluingIdentityCommaPinchedPrism_one,
    dgGluingCochainIdentityCommaPinchedInput_end]

def dgGluingCochainAugmentationHomotopy :
    SSet.Homotopy (complexPinchedMap.{u, max u v} f ≫ (pinchedComplexModelIso x y).inv)
      (complexPinchedMap.{u, max u v} g ≫ (pinchedComplexModelIso x y).inv) :=
  dgGluingHomotopyOfPrism (dgGluingCochainAugmentationPrism R E x y K f g h he)
    (dgGluingCochainAugmentationPrism_zero R E x y K f g h he)
    (dgGluingCochainAugmentationPrism_one R E x y K f g h he)

lemma dgGluingCochainAugmentationHomotopy_h :
    (dgGluingCochainAugmentationHomotopy R E x y K f g h he).h =
      (β_ (complexPinchedSpace.{u, max u v} K) (Δ[1] : SSet.{max u v})).hom ≫
        dgGluingCochainAugmentationPrism R E x y K f g h he := rfl

end SerrePositivity.InfinityCategories
