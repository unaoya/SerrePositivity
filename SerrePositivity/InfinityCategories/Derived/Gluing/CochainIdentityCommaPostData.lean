module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainPostBoundary
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaProjectionChainMaps

/-! 後合成した実 cochain 持ち上げは、同じ二射影・全 primitive を厳密に保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (E T : Type (max u v))
  [DGCategory R E] [DGCategory R T] (x y : E) (x' y' : T)
  (K : Complex R) (f g : K ⟶ homObject R E x y)
  (h : Cochain K (homObject R E x y) (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))
  (q : homObject R E x y ⟶ homObject R T x' y')
local notation "F" => dgGluingCochainIdentityCommaLift R E x y K f g h he
local notation "G" => dgGluingCochainIdentityCommaLift R T x' y' K (f ≫ q) (g ≫ q)
  (h.comp (Cochain.ofHom q) (add_zero (-1))) (dgGluingCochainPost_boundary f g h he q)

lemma dgGluingCochainIdentityCommaPost_source {P : Complex R} (t : P ⟶ K) :
    (t ≫ F) ≫ (dgCommaAugmentationTarget R E E (DGFunctor.id E)).map _ _ ≫ q =
      (t ≫ G) ≫ (dgCommaAugmentationTarget R T T (DGFunctor.id T)).map _ _ := by
  rw [dgGluingIdentityCommaTarget_map, dgGluingIdentityCommaTarget_map]
  simp only [Category.assoc, dgGluingCochainIdentityCommaLift_end]
  rw [← Category.assoc F, dgGluingCochainIdentityCommaLift_end]

lemma dgGluingCochainIdentityCommaPost_replacement {P : Complex R} (t : P ⟶ K) :
    (t ≫ F) ≫ (dgCommaAugmentationSource R E E (DGFunctor.id E)).map _ _ ≫ q =
      (t ≫ G) ≫ (dgCommaAugmentationSource R T T (DGFunctor.id T)).map _ _ := by
  change (t ≫ F) ≫ dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) _ _ ≫ q =
    (t ≫ G) ≫ dgFunctorCommaReplacementHomMap R T T (DGFunctor.id T) _ _
  simp only [Category.assoc, dgGluingCochainIdentityCommaLift_start]
  rw [← Category.assoc F, dgGluingCochainIdentityCommaLift_start]

lemma dgGluingCochainIdentityCommaPost_primitive :
    ((Cochain.ofHom F).comp (dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y))
      (zero_add (-1))).comp (Cochain.ofHom q) (add_zero (-1)) =
    (Cochain.ofHom G).comp (dgFunctorCommaPrimitive R T T (DGFunctor.id T)
      (dgGluingIdentityCommaObject R T x') (dgGluingIdentityCommaObject R T y'))
      (zero_add (-1)) := by
  rw [dgGluingCochainIdentityCommaLift_primitive, dgGluingCochainIdentityCommaLift_primitive,
    Cochain.neg_comp]

lemma dgGluingCochainIdentityCommaPost_pre_primitive {P : Complex R} (t : P ⟶ K) :
    ((Cochain.ofHom (t ≫ F)).comp (dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        (dgGluingIdentityCommaObject R E x) (dgGluingIdentityCommaObject R E y))
      (zero_add (-1))).comp (Cochain.ofHom q) (add_zero (-1)) =
    (Cochain.ofHom (t ≫ G)).comp (dgFunctorCommaPrimitive R T T (DGFunctor.id T)
      (dgGluingIdentityCommaObject R T x') (dgGluingIdentityCommaObject R T y'))
      (zero_add (-1)) := by
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain
    (Cochain.ofHom t) (Cochain.ofHom F) (dgFunctorCommaPrimitive R E E (DGFunctor.id E) _ _),
    Cochain.comp_assoc_of_first_is_zero_cochain (Cochain.ofHom t),
    dgGluingCochainIdentityCommaPost_primitive, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain]

end SerrePositivity.InfinityCategories
