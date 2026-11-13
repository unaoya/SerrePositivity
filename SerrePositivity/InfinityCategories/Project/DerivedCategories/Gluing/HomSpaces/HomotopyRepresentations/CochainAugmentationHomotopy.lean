module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.CochainIdentityCommaPinchedInput
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.IdentityCommaPinchedHomotopy

/-! 元の augmentation prism 自身から作る、任意の比較 cochain の全 pinched Hom ホモトピー。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) [DGCategory R E] (x y : E)
  (K : Complex R) (f g : K ⟶ homObject R E x y)
  (h : Cochain K (homObject R E x y) (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))

def dgGluingCochainAugmentationPrism :
    (Δ[1] : SSet.{max u v}) ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v} K ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R E x y :=
  ((Δ[1] : SSet.{max u v}) ◁
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPinchedInput R E x y K f g h he) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPinchedPrism R E x y

lemma dgGluingCochainAugmentationPrism_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ dgGluingCochainAugmentationPrism R E x y K f g h he =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v} f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y).inv := by
  rw [dgGluingCochainAugmentationPrism, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPinchedPrism_zero,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPinchedInput_start]

lemma dgGluingCochainAugmentationPrism_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ dgGluingCochainAugmentationPrism R E x y K f g h he =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v} g ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y).inv := by
  rw [dgGluingCochainAugmentationPrism, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPinchedPrism_one,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPinchedInput_end]

def dgGluingCochainAugmentationHomotopy :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v} f ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y).inv)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v} g ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y).inv) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyOfPrism (dgGluingCochainAugmentationPrism R E x y K f g h he)
    (dgGluingCochainAugmentationPrism_zero R E x y K f g h he)
    (dgGluingCochainAugmentationPrism_one R E x y K f g h he)

lemma dgGluingCochainAugmentationHomotopy_h :
    (dgGluingCochainAugmentationHomotopy R E x y K f g h he).h =
      (β_ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v} K) (Δ[1] : SSet.{max u v})).hom ≫
        dgGluingCochainAugmentationPrism R E x y K f g h he := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
