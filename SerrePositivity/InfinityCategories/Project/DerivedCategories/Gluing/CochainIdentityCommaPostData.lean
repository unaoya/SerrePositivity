module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CochainPostBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityCommaProjectionChainMaps

/-! 後合成した実 cochain 持ち上げは、同じ二射影・全 primitive を厳密に保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (E T : Type (max u v))
  [DGCategory R E] [DGCategory R T] (x y : E) (x' y' : T)
  (K : Complex R) (f g : K ⟶ homObject R E x y)
  (h : Cochain K (homObject R E x y) (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))
  (q : homObject R E x y ⟶ homObject R T x' y')
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift R E x y K f g h he
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift R T x' y' K (f ≫ q) (g ≫ q)
  (h.comp (Cochain.ofHom q) (add_zero (-1))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainPost_boundary f g h he q)

lemma dgGluingCochainIdentityCommaPost_source {P : Complex R} (t : P ⟶ K) :
    (t ≫ F) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R E E (DGFunctor.id E)).map _ _ ≫ q =
      (t ≫ G) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTarget R T T (DGFunctor.id T)).map _ _ := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaTarget_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaTarget_map]
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift_end]
  rw [← Category.assoc F, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift_end]

lemma dgGluingCochainIdentityCommaPost_replacement {P : Complex R} (t : P ⟶ K) :
    (t ≫ F) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R E E (DGFunctor.id E)).map _ _ ≫ q =
      (t ≫ G) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R T T (DGFunctor.id T)).map _ _ := by
  change (t ≫ F) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) _ _ ≫ q =
    (t ≫ G) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R T T (DGFunctor.id T) _ _
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift_start]
  rw [← Category.assoc F, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift_start]

lemma dgGluingCochainIdentityCommaPost_primitive :
    ((Cochain.ofHom F).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y))
      (zero_add (-1))).comp (Cochain.ofHom q) (add_zero (-1)) =
    (Cochain.ofHom G).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R T T (DGFunctor.id T)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R T x') (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R T y'))
      (zero_add (-1)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift_primitive, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaLift_primitive,
    Cochain.neg_comp]

lemma dgGluingCochainIdentityCommaPost_pre_primitive {P : Complex R} (t : P ⟶ K) :
    ((Cochain.ofHom (t ≫ F)).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y))
      (zero_add (-1))).comp (Cochain.ofHom q) (add_zero (-1)) =
    (Cochain.ofHom (t ≫ G)).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R T T (DGFunctor.id T)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R T x') (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R T y'))
      (zero_add (-1)) := by
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain
    (Cochain.ofHom t) (Cochain.ofHom F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E) _ _),
    Cochain.comp_assoc_of_first_is_zero_cochain (Cochain.ofHom t),
    dgGluingCochainIdentityCommaPost_primitive, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
