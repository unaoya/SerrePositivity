module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationCochainInput
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationRawFaces
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeIdentityAugmentationPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeDerivedNormalizationCubes
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseSquareReindex

/-! 後 cube の全正規化面を、元二作用・負 primitive だけによる同じ明示 cochain 四角形へ戻す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "RM" => RightModule R C
local notation "Q" => DGFunctorCommaObject R (RightModule R C) (RightModule R C)
  (DGFunctor.id (RightModule R C))
local notation "IX" => dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => dgGluingNativeIdentityCommaObject R C D M Y
local notation "NX" => dgGluingIdentityCommaObject R (RightModule R C) (representable R X.left)
local notation "NY" => dgGluingIdentityCommaObject R (RightModule R C) (M.rightAt Y.right)

abbrev dgGluingNativeModuleCochainRawInput :=
  dgGluingCochainIdentityCommaPinchedInput.{u, max (u + 1) v}
    R RM (representable R X.left) (M.rightAt Y.right) (dgGluingHomComplex R C D M X Y)
    ((dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y) ≫
      (dgYonedaIso R X.left (M.rightAt Y.right)).inv)
    ((dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y) ≫
      (dgYonedaIso R X.left (M.rightAt Y.right)).inv)
    ((-dgGluingHomPrimitive R C D M X Y).comp
      (Cochain.ofHom (dgYonedaIso R X.left (M.rightAt Y.right)).inv) (add_zero (-1)))
    (dgGluingNativeNormalizedCochain_boundary R C D M X Y)

def dgGluingNativeModuleIdentityHomSquare :=
  ((Δ[1] : SSet.{max (u + 1) v}) ◁ intervalMappingUncurry
    (pinchedHomToIntervalMappingSpace (X := dgNerve R Q) (Simplex.vertex NX) (Simplex.vertex NY))) ≫
      dgGluingModuleIdentityAugmentationPrism R C

def dgGluingNativeModuleCochainSquare :=
  (Δ[1] ◁ (Δ[1] ◁ dgGluingNativeModuleCochainRawInput R C D M X Y)) ≫
    dgGluingNativeModuleIdentityHomSquare R C D M X Y

lemma dgGluingNativePostNormalizeRawCube_face_factor :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 (DGNerve.pinchedHom R Q IX IY))) ≫
        dgGluingNativePostNormalizeRawCube R C D M X Y =
      (Δ[1] ◁ (Δ[1] ◁ pinchedHomChainMap (D := Q) (E := Q)
        (dgGluingIdentityCommaNormalizeHom R RM IX IY))) ≫
          dgGluingNativeModuleIdentityHomSquare R C D M X Y := by
  rw [dgGluingNativePostNormalizeRawCube_normalized_face]
  change (Δ[1] ◁ intervalMappingUncurry (pinchedHomChainMap (D := Q) (E := Q)
      (dgGluingIdentityCommaNormalizeHom R RM IX IY) ≫
        pinchedHomToIntervalMappingSpace (X := dgNerve R Q)
          (Simplex.vertex NX) (Simplex.vertex NY))) ≫
      dgGluingModuleIdentityAugmentationPrism R C = _
  rw [intervalMappingUncurry_precomp]
  rfl

lemma dgGluingNativePostNormalizeCube_cochain_face :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 _)) ≫ dgGluingNativePostNormalizeCube R C D M X Y =
      (Δ[1] ◁ (Δ[1] ◁ dgGluingNativeModuleCochainModelInput R C D M X Y)) ≫
        dgGluingUliftSquareFamily.{max (u + 1) v, max (u + 1) v w}
          (dgGluingNativeModuleCochainSquare R C D M X Y) := by
  rw [dgGluingNativePostNormalizeCube, dgGluingNativeNormalizationCube_inner,
    dgGluingNativePostNormalizeRawCube_face_factor]
  exact dgGluingUliftSquareFamily_reindex_eq.{max (u + 1) v, max (u + 1) v w}
    (dgGluingNativeModuleIdentityHomSquare R C D M X Y)
    (pinchedHomChainMap (D := Q) (E := Q) (dgGluingIdentityCommaNormalizeHom R RM IX IY))
    (dgGluingNativeModuleCochainRawInput R C D M X Y)
    (dgGluingNativeNormalizationHomInput R C D M X Y)
    (dgGluingNativeModuleCochainModelInput R C D M X Y)
    (dgGluingNativeNormalizationHomInput_cochain R C D M X Y)

lemma dgGluingNativeDerivedPostNormalizeCube_cochain_face :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 _)) ≫
        dgGluingNativeDerivedPostNormalizeCube R C D M X Y =
      (Δ[1] ◁ (Δ[1] ◁ dgGluingNativeModuleCochainModelInput R C D M X Y)) ≫
        dgGluingUliftSquareFamily.{max (u + 1) v, max (u + 1) v w}
          (dgGluingNativeModuleCochainSquare R C D M X Y) ≫
            dgGluingUniverseModuleDerivedComparison.{u, v, w} R C := by
  rw [dgGluingNativeDerivedPostNormalizeCube, ← Category.assoc,
    dgGluingNativePostNormalizeCube_cochain_face, Category.assoc]

end SerrePositivity.InfinityCategories
