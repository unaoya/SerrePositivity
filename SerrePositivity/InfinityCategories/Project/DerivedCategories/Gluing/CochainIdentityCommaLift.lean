module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityCommaHomLift

/-! δh = g − f の実 cochain を、同じ始端 f・終端 g と負比較成分の comma 射へ移す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] (x y : E)
  (K : Complex R) (f g : K ⟶ homObject R E x y)
  (h : Cochain K (homObject R E x y) (-1)) (he : δ (-1) 0 h = Cochain.ofHom (g - f))

include he in
lemma dgGluingCochainIdentityCommaLift_boundary :
    δ (-1) 0 (-h) + Cochain.ofHom (g - f) = 0 := by
  rw [δ_neg, he, neg_add_cancel]

def dgGluingCochainIdentityCommaLift :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaHomLift R E x y K g f (-h)
    (dgGluingCochainIdentityCommaLift_boundary R E x y K f g h he)

lemma dgGluingCochainIdentityCommaLift_start :
    dgGluingCochainIdentityCommaLift R E x y K f g h he ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y) = f :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaHomLift_replacement _ _ _ _ _ _ _ _ _

lemma dgGluingCochainIdentityCommaLift_end :
    dgGluingCochainIdentityCommaLift R E x y K f g h he ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R E E (DGFunctor.id E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y) = g :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaHomLift_source _ _ _ _ _ _ _ _ _

lemma dgGluingCochainIdentityCommaLift_primitive :
    (Cochain.ofHom (dgGluingCochainIdentityCommaLift R E x y K f g h he)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E x)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E y)) (zero_add (-1)) = -h :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaHomLift_primitive _ _ _ _ _ _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
