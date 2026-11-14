module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.IdentityComparisons.IdentityCommaPrismProjection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.ComplexPinchedInputChainMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.CochainAugmentationHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.CochainIdentityCommaProjectionInput

/-! 射影が比較 cochain を消す場合、同じ明示 augmentation の全区間は射影後に定値になる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory
open CartesianMonoidalCategory
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (x y : E)
  (K : _root_.SerrePositivity.DifferentialGraded.Complex R) (f g : K ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E x y)
  (h : Cochain K (_root_.SerrePositivity.DifferentialGraded.homObject R E x y) (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))
  {T : Type (max u v)} [_root_.SerrePositivity.DifferentialGraded.DGCategory R T] {x' y' : T}
  (q : _root_.SerrePositivity.DifferentialGraded.homObject R E x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R T x' y')
  (hp : g ≫ q = f ≫ q)
  (hz : h.comp (Cochain.ofHom q) (add_zero (-1)) = 0)

include hp hz in
lemma dgGluingCochainAugmentationPrism_post_zero :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism R E x y K f g h he ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap q =
      snd Δ[1] (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v} K) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v} (f ≫ q) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x' y').inv := by
  let φ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).inv ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift R E x y K f g h he
  obtain ⟨hpair, hprim⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift_projection_input R E x y K
    f g h he q hp hz (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).inv
  have hrep : φ ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E)).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).inv ≫ f := by
    change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).inv ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift R E x y K f g h he) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) _ _ = _
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift_start]
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPrism_input_post_zero R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGComplexPinchedModel.{u, max u v} K) E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSource _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedTarget _)
    x y φ q hpair hprim
  have hnorm : φ ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E)).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y) ≫ q =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexUnitHomIso K).inv ≫ f ≫ q := by
    rw [← Category.assoc, hrep, Category.assoc]
  rw [hnorm, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedInput_eq_chainMap (f ≫ q)] at ht
  have hi := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedInput_eq_chainMap
    (E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
    (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift R E x y K f g h he)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPinchedInput,
    hi, Category.assoc]
  exact ht

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
