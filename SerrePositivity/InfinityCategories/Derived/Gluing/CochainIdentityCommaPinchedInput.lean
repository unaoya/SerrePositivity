module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainIdentityCommaLift
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaProjectionChainMaps
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedModelInverseNaturality

/-! 任意の比較 cochain の実入力族を、同じ f・g の全 pinched 族を保って comma Hom へ入れる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (E : Type (max u v)) [DGCategory R E] (x y : E)
  (K : Complex R) (f g : K ⟶ homObject R E x y)
  (h : Cochain K (homObject R E x y) (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))

def dgGluingCochainIdentityCommaPinchedInput :
    complexPinchedSpace.{u, max u v} K ⟶
      DGNerve.pinchedHom R (DGFunctorCommaObject R E E (DGFunctor.id E))
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) :=
  complexPinchedMap.{u, max u v} (dgGluingCochainIdentityCommaLift R E x y K f g h he) ≫
    (pinchedComplexModelIso (dgGluingIdentityCommaObject R E x)
      (dgGluingIdentityCommaObject R E y)).inv

lemma dgGluingCochainIdentityCommaPinchedInput_start :
    dgGluingCochainIdentityCommaPinchedInput R E x y K f g h he ≫
        dgGluingIdentityCommaReplacementPinchedMap R E x y =
      complexPinchedMap.{u, max u v} f ≫ (pinchedComplexModelIso x y).inv := by
  rw [dgGluingCochainIdentityCommaPinchedInput, Category.assoc,
    dgGluingIdentityCommaReplacementPinchedMap_chainMap R E x y,
    ← dgGluingComplexPinchedModelInverse_naturality,
    ← Category.assoc, ← complexPinchedMap_comp, dgGluingCochainIdentityCommaLift_start]

lemma dgGluingCochainIdentityCommaPinchedInput_end :
    dgGluingCochainIdentityCommaPinchedInput R E x y K f g h he ≫
        dgGluingIdentityCommaSourcePinchedMap R E x y =
      complexPinchedMap.{u, max u v} g ≫ (pinchedComplexModelIso x y).inv := by
  rw [dgGluingCochainIdentityCommaPinchedInput, Category.assoc,
    dgGluingIdentityCommaSourcePinchedMap_chainMap R E x y,
    ← dgGluingComplexPinchedModelInverse_naturality,
    ← Category.assoc, ← complexPinchedMap_comp, dgGluingCochainIdentityCommaLift_end]

end SerrePositivity.InfinityCategories
