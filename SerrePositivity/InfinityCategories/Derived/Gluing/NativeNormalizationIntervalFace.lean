module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeCochainPrismIntervalSquare
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeModuleNormalizedPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.PrismIntervalSquare

/-! 実後 cube の正規化面は、同じ元 Hom の正規化 pinched prism の全区間評価。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "RM" => RightModule R C

def dgGluingNativeModulePinchedIntervalEvaluation :
    (Δ[1] : SSet.{max (u + 1) v}) ⊗
      DGNerve.pinchedHom R RM (representable R X.left) (M.rightAt Y.right) ⟶ dgNerve R RM :=
  intervalMappingUncurry (pinchedHomToIntervalMappingSpace (X := dgNerve R RM)
    (Simplex.vertex (representable R X.left)) (Simplex.vertex (M.rightAt Y.right)))

def dgGluingNativeModuleNormalizedIntervalEvaluation :=
  dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1
    (dgGluingNativeModulePinchedIntervalEvaluation R C D M X Y)

lemma dgGluingNativePostNormalizeCube_interval_face :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 _)) ≫ dgGluingNativePostNormalizeCube R C D M X Y =
      dgGluingPrismIntervalSquare (dgGluingNativeModuleNormalizedPrism R C D M X Y)
        (dgGluingNativeModuleNormalizedIntervalEvaluation R C D M X Y) := by
  have hr : dgGluingNativeModuleCochainSquare R C D M X Y =
      dgGluingPrismIntervalSquare (dgGluingNativeModuleCochainPrism R C D M X Y)
        (dgGluingNativeModulePinchedIntervalEvaluation R C D M X Y) :=
    dgGluingNativeModuleCochainSquare_interval R C D M X Y
  rw [dgGluingNativePostNormalizeCube_cochain_face, hr, dgGluingUliftPrismIntervalSquare,
    dgGluingPrismIntervalSquare_precomp, dgGluingNativeModuleNormalizedPrism_cochain]
  rfl

lemma dgGluingNativeDerivedPostNormalizeCube_interval_face :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 _)) ≫
        dgGluingNativeDerivedPostNormalizeCube R C D M X Y =
      dgGluingPrismIntervalSquare (dgGluingNativeModuleNormalizedPrism R C D M X Y)
        (dgGluingNativeModuleNormalizedIntervalEvaluation R C D M X Y ≫
          dgGluingUniverseModuleDerivedComparison.{u, v, w} R C) := by
  rw [dgGluingNativeDerivedPostNormalizeCube, ← Category.assoc,
    dgGluingNativePostNormalizeCube_interval_face, dgGluingPrismIntervalSquare_post]

end SerrePositivity.InfinityCategories
