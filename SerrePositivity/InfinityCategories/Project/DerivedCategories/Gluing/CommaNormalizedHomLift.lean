module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaNormalizedHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityCommaHomLift

/-! 実閉射による正規化と、同じ二作用・primitive の明示 mapping-cocone lift は厳密に一致する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)

abbrev dgGluingCommaNormalizedSource :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ⟶ homObject R E X.replacement (F.obj Y.source) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F X Y ≫
    eHomWhiskerRight (Complex R) X.augmentation
      (ForgetEnrichment.of (Complex R) (F.obj Y.source))

abbrev dgGluingCommaNormalizedReplacement :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ⟶ homObject R E X.replacement (F.obj Y.source) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y ≫
    eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement) Y.augmentation

lemma dgGluingCommaNormalizedPrimitive_boundary :
    δ (-1) 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y) +
      Cochain.ofHom (dgGluingCommaNormalizedSource R C E F X Y -
        dgGluingCommaNormalizedReplacement R C E F X Y) = 0 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive_boundary R C E F X Y

def dgGluingCommaNormalizedHomLift :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R E E (DGFunctor.id E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E (F.obj Y.source)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaHomLift R E X.replacement (F.obj Y.source) _
    (dgGluingCommaNormalizedSource R C E F X Y)
    (dgGluingCommaNormalizedReplacement R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y)
    (dgGluingCommaNormalizedPrimitive_boundary R C E F X Y)

lemma dgGluingCommaNormalizedHom_eq_lift :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaNormalizedHom R C E F X Y = dgGluingCommaNormalizedHomLift R C E F X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHom_ext R E E (DGFunctor.id E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E (F.obj Y.source)) _
  · rw [dgGluingCommaNormalizedHomLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaHomLift_source,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaNormalizedHom_source]
  · rw [dgGluingCommaNormalizedHomLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaHomLift_replacement,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaNormalizedHom_replacement]
  · change (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaNormalizedHom R C E F X Y)).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E) _ _) (zero_add (-1)) =
      (Cochain.ofHom (dgGluingCommaNormalizedHomLift R C E F X Y)).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E) _ _) (zero_add (-1))
    rw [dgGluingCommaNormalizedHomLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaNormalizedHom_primitive,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaHomLift_primitive]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
