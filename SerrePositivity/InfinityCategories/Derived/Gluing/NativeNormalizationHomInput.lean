module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationCubes
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizedHom
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseHomChainMapComposition

/-! native cube の同じ入力に実閉射の正規化を適用すると、元 Hom の同じ正規化鎖写像になる。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "Q" => DGFunctorCommaObject R (RightModule R C) (RightModule R C)
  (DGFunctor.id (RightModule R C))
local notation "IX" => dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => dgGluingNativeIdentityCommaObject R C D M Y

lemma dgGluingNativeNormalizationHomInput_normalized :
    dgGluingNativeNormalizationHomInput R C D M X Y ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
          (pinchedHomChainMap (D := Q) (E := Q)
            (dgGluingIdentityCommaNormalizeHom R (RightModule R C) IX IY)) =
      dgGluingUniverseHomChainMap.{u, max u v w, max (u + 1) v, max (u + 1) v w}
        (C := DGGluingObject R C D M) (D := Q) (x := X) (y := Y)
        (x' := dgGluingIdentityCommaObject R (RightModule R C) (representable R X.left))
        (y' := dgGluingIdentityCommaObject R (RightModule R C) (M.rightAt Y.right))
        (dgGluingNativeNormalizedHom R C D M X Y) :=
  dgGluingUniverseHomChainMap_post.{u, max u v w, max (u + 1) v, max (u + 1) v w}
    (C := DGGluingObject R C D M) (D := Q) (E := Q)
    (x := X) (y := Y) (x' := IX) (y' := IY)
    (x'' := dgGluingIdentityCommaObject R (RightModule R C) (representable R X.left))
    (y'' := dgGluingIdentityCommaObject R (RightModule R C) (M.rightAt Y.right))
    ((dgGluingNativeIdentityCommaFunctor R C D M).map X Y)
    (dgGluingIdentityCommaNormalizeHom R (RightModule R C) IX IY)

end SerrePositivity.InfinityCategories
