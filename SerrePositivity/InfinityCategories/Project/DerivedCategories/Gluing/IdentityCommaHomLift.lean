module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityCommaObject

/-! 任意の二鎖写像と比較 cochain を、恒等 augmentation の同じ実 comma Hom へ持ち上げる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] (x y : E)

lemma dgGluingIdentityCommaDifference :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R E E (DGFunctor.id E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y) =
      (biprod.fst : homObject R E x y ⊞ homObject R E x y ⟶ homObject R E x y) - biprod.snd := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject, DGFunctor.id,
    EnrichedFunctor.id]
  simp only [eHomWhiskerRight_id, eHomWhiskerLeft_id, Category.comp_id]
  rfl

variable (K : Complex R) (a b : K ⟶ homObject R E x y)
  (h : Cochain K (homObject R E x y) (-1)) (he : δ (-1) 0 h + Cochain.ofHom (a - b) = 0)

lemma dgGluingIdentityCommaDifference_lift :
    biprod.lift a b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R E E (DGFunctor.id E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y) = a - b := by
  have h := congrArg (fun q : homObject R E x y ⊞ homObject R E x y ⟶ homObject R E x y =>
    biprod.lift a b ≫ q) (dgGluingIdentityCommaDifference R E x y)
  exact h.trans (by simp only [Preadditive.comp_sub, biprod.lift_fst, biprod.lift_snd])

def dgGluingIdentityCommaHomLift : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R E E (DGFunctor.id E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift R E E (DGFunctor.id E) _ _ K a b h (by
    rw [dgGluingIdentityCommaDifference_lift R E x y K a b]
    exact he)

lemma dgGluingIdentityCommaHomLift_source :
    dgGluingIdentityCommaHomLift R E x y K a b h he ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R E E
      (DGFunctor.id E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y) = a :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_source _ _ _ _ _ _ _ _ _ _ _

lemma dgGluingIdentityCommaHomLift_replacement :
    dgGluingIdentityCommaHomLift R E x y K a b h he ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R E E
      (DGFunctor.id E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y) = b :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_replacement _ _ _ _ _ _ _ _ _ _ _

lemma dgGluingIdentityCommaHomLift_primitive :
    (Cochain.ofHom (dgGluingIdentityCommaHomLift R E x y K a b h he)).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y)) (zero_add (-1)) = h := by
  apply Cochain.ext
  intro p q hpq
  simp only [dgGluingIdentityCommaHomLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact mappingCocone.lift_f_snd_v _ _ _ _ p q hpq

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
