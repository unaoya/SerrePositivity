module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IdentityCommaGeneralDifference
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaComparison

/-! 任意関手の comma を、その同じ実 augmentation を持つ標的恒等 comma へ移す全 Hom 鎖写像。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)

def dgGluingCommaImageObject (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E) where
  source := F.obj X.source
  replacement := X.replacement
  augmentation := X.augmentation

lemma dgGluingCommaImage_difference (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) :
    biprod.lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F X Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R E E (DGFunctor.id E)
        (dgGluingCommaImageObject R C E F X) (dgGluingCommaImageObject R C E F Y) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaBoundary R C E F X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaGeneralDifference_lift R E _ _ _ _ _

def dgGluingCommaImageHomMap (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R E E (DGFunctor.id E)
        (dgGluingCommaImageObject R C E F X) (dgGluingCommaImageObject R C E F Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift R E E (DGFunctor.id E) _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F X Y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y) (by
      rw [dgGluingCommaImage_difference]
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive_boundary R C E F X Y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
