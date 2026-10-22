module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismProjection
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedInputChainMap
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainAugmentationHomotopy
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainIdentityCommaProjectionInput

/-! 射影が比較 cochain を消す場合、同じ明示 augmentation の全区間は射影後に定値になる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory
open CartesianMonoidalCategory DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) [DGCategory R E] (x y : E)
  (K : Complex R) (f g : K ⟶ homObject R E x y)
  (h : Cochain K (homObject R E x y) (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))
  {T : Type (max u v)} [DGCategory R T] {x' y' : T}
  (q : homObject R E x y ⟶ homObject R T x' y')
  (hp : g ≫ q = f ≫ q)
  (hz : h.comp (Cochain.ofHom q) (add_zero (-1)) = 0)

include hp hz in
lemma dgGluingCochainAugmentationPrism_post_zero :
    dgGluingCochainAugmentationPrism R E x y K f g h he ≫ pinchedHomChainMap q =
      snd Δ[1] (complexPinchedSpace.{u, max u v} K) ≫
        complexPinchedMap.{u, max u v} (f ≫ q) ≫ (pinchedComplexModelIso x' y').inv := by
  let φ := (complexUnitHomIso K).inv ≫ dgGluingCochainIdentityCommaLift R E x y K f g h he
  obtain ⟨hpair, hprim⟩ := dgGluingCochainIdentityCommaLift_projection_input R E x y K
    f g h he q hp hz (complexUnitHomIso K).inv
  have hrep : φ ≫ (dgCommaAugmentationSource R E E (DGFunctor.id E)).map
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) =
      (complexUnitHomIso K).inv ≫ f := by
    change ((complexUnitHomIso K).inv ≫ dgGluingCochainIdentityCommaLift R E x y K f g h he) ≫
      dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) _ _ = _
    rw [Category.assoc, dgGluingCochainIdentityCommaLift_start]
  have ht := dgGluingIdentityCommaPrism_input_post_zero R
    (DGComplexPinchedModel.{u, max u v} K) E (complexPinchedSource _) (complexPinchedTarget _)
    x y φ q hpair hprim
  have hnorm : φ ≫ (dgCommaAugmentationSource R E E (DGFunctor.id E)).map
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y) ≫ q =
      (complexUnitHomIso K).inv ≫ f ≫ q := by
    rw [← Category.assoc, hrep, Category.assoc]
  rw [hnorm, ← dgGluingComplexPinchedInput_eq_chainMap (f ≫ q)] at ht
  have hi := dgGluingComplexPinchedInput_eq_chainMap
    (E := DGFunctorCommaObject R E E (DGFunctor.id E))
    (x := dgGluingIdentityCommaObject R E x) (y := dgGluingIdentityCommaObject R E y)
    (dgGluingCochainIdentityCommaLift R E x y K f g h he)
  rw [dgGluingCochainAugmentationPrism, dgGluingCochainIdentityCommaPinchedInput,
    hi, Category.assoc]
  exact ht

end SerrePositivity.InfinityCategories
