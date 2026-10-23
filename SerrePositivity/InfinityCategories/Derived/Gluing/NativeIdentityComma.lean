module
public import SerrePositivity.InfinityCategories.Derived.Gluing.Category
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaImageFunctor

/-! 元の gluing 対象・Hom を変えず、同じ augmentation を持つ加群恒等 comma へ移す実 dg 関手。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingNativeIdentityCommaObject (X : DGGluingObject R C D M) :
    DGFunctorCommaObject R (RightModule R C) (RightModule R C) (DGFunctor.id (RightModule R C)) :=
  dgGluingCommaImageObject R D (RightModule R C) M.toFunctor (dgGluingCommaObject R C D M X)

def dgGluingNativeIdentityCommaFunctor : DGFunctor R (DGGluingObject R C D M)
    (DGFunctorCommaObject R (RightModule R C) (RightModule R C) (DGFunctor.id (RightModule R C))) :=
  (dgGluingToComma R C D M).comp (dgGluingCommaImageFunctor R D (RightModule R C) M.toFunctor)

lemma dgGluingNativeIdentityCommaFunctor_obj (X : DGGluingObject R C D M) :
    (dgGluingNativeIdentityCommaFunctor R C D M).obj X =
      dgGluingNativeIdentityCommaObject R C D M X := rfl

lemma dgGluingNativeIdentityCommaFunctor_map (X Y : DGGluingObject R C D M) :
    (dgGluingNativeIdentityCommaFunctor R C D M).map X Y =
      (dgGluingToComma R C D M).map X Y ≫
        dgGluingCommaImageHomMap R D (RightModule R C) M.toFunctor
          (dgGluingCommaObject R C D M X) (dgGluingCommaObject R C D M Y) := rfl

end SerrePositivity.InfinityCategories
