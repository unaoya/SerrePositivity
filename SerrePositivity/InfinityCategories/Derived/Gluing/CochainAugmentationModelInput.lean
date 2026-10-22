module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainAugmentationHomotopy
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedInputChainMap

/-! 元 dg Hom の模型同型で制限すると、明示 cochain prism の入力は同じ実 comma 持ち上げになる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C E : Type (max u v)) [DGCategory R C] [DGCategory R E]
  (a b : C) (x y : E)
  (f g : homObject R C a b ⟶ homObject R E x y)
  (h : Cochain (homObject R C a b) (homObject R E x y) (-1))
  (he : δ (-1) 0 h = Cochain.ofHom (g - f))

lemma dgGluingCochainIdentityCommaPinchedInput_model :
    (pinchedComplexModelIso a b).hom ≫
        dgGluingCochainIdentityCommaPinchedInput R E x y (homObject R C a b) f g h he =
      pinchedHomChainMap (D := C) (E := DGFunctorCommaObject R E E (DGFunctor.id E))
        (x := a) (y := b) (x' := dgGluingIdentityCommaObject R E x)
        (y' := dgGluingIdentityCommaObject R E y)
        (dgGluingCochainIdentityCommaLift R E x y (homObject R C a b) f g h he) := by
  have hi := dgGluingComplexPinchedInput_eq_chainMap
    (E := DGFunctorCommaObject R E E (DGFunctor.id E))
    (x := dgGluingIdentityCommaObject R E x) (y := dgGluingIdentityCommaObject R E y)
    (dgGluingCochainIdentityCommaLift R E x y (homObject R C a b) f g h he)
  rw [dgGluingCochainIdentityCommaPinchedInput, hi,
    dgGluingPinchedComplexModelIso_hom, ← pinchedHomChainMap_comp]
  congr 1
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

lemma dgGluingCochainAugmentationPrism_model_input :
    (Δ[1] ◁ (pinchedComplexModelIso a b).hom) ≫
        dgGluingCochainAugmentationPrism R E x y (homObject R C a b) f g h he =
      (Δ[1] ◁ pinchedHomChainMap
        (dgGluingCochainIdentityCommaLift R E x y (homObject R C a b) f g h he)) ≫
        dgGluingIdentityCommaPinchedPrism R E x y := by
  rw [dgGluingCochainAugmentationPrism, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingCochainIdentityCommaPinchedInput_model]

end SerrePositivity.InfinityCategories
