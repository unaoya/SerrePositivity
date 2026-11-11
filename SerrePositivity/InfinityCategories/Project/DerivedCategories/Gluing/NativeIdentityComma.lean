module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Category
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaImageFunctor

/-! 元の gluing 対象・Hom を変えず、同じ augmentation を持つ加群恒等 comma へ移す実 dg 関手。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingNativeIdentityCommaObject (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R C) (RightModule R C) (DGFunctor.id (RightModule R C)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageObject R D (RightModule R C) M.toFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X)

def dgGluingNativeIdentityCommaFunctor : DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R C) (RightModule R C) (DGFunctor.id (RightModule R C))) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageFunctor R D (RightModule R C) M.toFunctor)

lemma dgGluingNativeIdentityCommaFunctor_obj (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (dgGluingNativeIdentityCommaFunctor R C D M).obj X =
      dgGluingNativeIdentityCommaObject R C D M X := rfl

lemma dgGluingNativeIdentityCommaFunctor_map (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    (dgGluingNativeIdentityCommaFunctor R C D M).map X Y =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).map X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap R D (RightModule R C) M.toFunctor
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M X) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M Y) := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
