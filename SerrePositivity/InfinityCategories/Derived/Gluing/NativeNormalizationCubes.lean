module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationRawCubes
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseCubeBoundary
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseHomChainMap

/-! 元の一般宇宙の gluing Hom 全体から、元加群 nerve の共通宇宙へ実正規化 cube を供給。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "E" => RightModule R C
local notation "Q" => DGFunctorCommaObject R (RightModule R C) (RightModule R C)
  (DGFunctor.id (RightModule R C))
local notation "IX" => dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => dgGluingNativeIdentityCommaObject R C D M Y

def dgGluingNativeNormalizationHomInput :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y) ⟶
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (DGNerve.pinchedHom R Q IX IY) :=
  dgGluingUniverseHomChainMap.{u, max u v w, max (u + 1) v, max (u + 1) v w}
    ((dgGluingNativeIdentityCommaFunctor R C D M).map X Y)

def dgGluingNativeNormalizationCube
    (V : (Δ[1] : SSet.{max (u + 1) v}) ⊗
      (Δ[1] ⊗ (Δ[1] ⊗ DGNerve.pinchedHom R Q IX IY)) ⟶ dgNerve R E) :
    (Δ[1] : SSet.{max (u + 1) v w}) ⊗
      (Δ[1] ⊗ (Δ[1] ⊗ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (DGNerve.pinchedHom R (DGGluingObject R C D M) X Y))) ⟶
          (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj (dgNerve R E) :=
  (Δ[1] ◁ (Δ[1] ◁ (Δ[1] ◁ dgGluingNativeNormalizationHomInput R C D M X Y))) ≫
    dgGluingUliftCubeFamily.{max (u + 1) v, max (u + 1) v w} V

def dgGluingNativePreNormalizeCube :=
  dgGluingNativeNormalizationCube R C D M X Y (dgGluingNativePreNormalizeRawCube R C D M X Y)

def dgGluingNativePostNormalizeCube :=
  dgGluingNativeNormalizationCube R C D M X Y (dgGluingNativePostNormalizeRawCube R C D M X Y)

end SerrePositivity.InfinityCategories
