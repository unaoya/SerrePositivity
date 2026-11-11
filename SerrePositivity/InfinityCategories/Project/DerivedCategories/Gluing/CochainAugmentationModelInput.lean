module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CochainAugmentationHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexPinchedInputChainMap

/-! 元 dg Hom の模型同型で制限すると、明示 cochain prism の入力は同じ実 comma 持ち上げになる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C E : Type (max u v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  (a b : C) (x y : E)
  (f g : _root_.SerrePositivity.DifferentialGraded.homObject R C a b ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E x y)
  (h : Cochain (_root_.SerrePositivity.DifferentialGraded.homObject R C a b) (_root_.SerrePositivity.DifferentialGraded.homObject R E x y) (-1))
  (he : δ (-1) 0 h = Cochain.ofHom (g - f))

lemma dgGluingCochainIdentityCommaPinchedInput_model :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso a b).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPinchedInput R E x y (homObject R C a b) f g h he =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := C) (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
        (x := a) (y := b) (x' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x)
        (y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift R E x y (homObject R C a b) f g h he) := by
  have hi := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedInput_eq_chainMap
    (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
    (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift R E x y (homObject R C a b) f g h he)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPinchedInput, hi,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedComplexModelIso_hom, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp]
  congr 1
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

lemma dgGluingCochainAugmentationPrism_model_input :
    (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso a b).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism R E x y (homObject R C a b) f g h he =
      (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift R E x y (homObject R C a b) f g h he)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPinchedPrism R E x y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingCochainIdentityCommaPinchedInput_model]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
