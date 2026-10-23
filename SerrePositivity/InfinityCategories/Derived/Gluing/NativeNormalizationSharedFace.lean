module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeDerivedNormalizationCubes

/-! 実前合成 cube の正規化面と実後合成 cube の始面は、元 Hom 全体にわたり同じ二次元族。 -/
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
local notation "RM" => RightModule R C
local notation "Q" => DGFunctorCommaObject R (RightModule R C) (RightModule R C)
  (DGFunctor.id (RightModule R C))
local notation "IX" => dgGluingNativeIdentityCommaObject R C D M X
local notation "IY" => dgGluingNativeIdentityCommaObject R C D M Y

lemma dgGluingNativeNormalizationRawCube_shared_face :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 (DGNerve.pinchedHom R Q IX IY))) ≫
        dgGluingNativePreNormalizeRawCube R C D M X Y =
      (Δ[1] ◁ prismEndpoint 0 (Δ[1] ⊗ DGNerve.pinchedHom R Q IX IY)) ≫
        dgGluingNativePostNormalizeRawCube R C D M X Y := by
  have hi := (dgGluingIdentityCommaPreNormalizeCube_interval_zero R RM IX IY (𝟙 _)).trans
    (dgGluingIdentityCommaPostNormalizeCube_source R RM IX IY (𝟙 _)).symm
  have hh := congrArg (fun k => k ≫
    dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R RM)) hi
  dsimp only [dgGluingNativePreNormalizeRawCube, dgGluingNativePostNormalizeRawCube]
  simpa only [Category.assoc] using hh

lemma dgGluingNativeNormalizationCube_shared_face :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 _)) ≫ dgGluingNativePreNormalizeCube R C D M X Y =
      (Δ[1] ◁ prismEndpoint 0 _) ≫ dgGluingNativePostNormalizeCube R C D M X Y := by
  rw [dgGluingNativePreNormalizeCube, dgGluingNativePostNormalizeCube,
    dgGluingNativeNormalizationCube_inner, dgGluingNativeNormalizationCube_middle,
    dgGluingNativeNormalizationRawCube_shared_face]

lemma dgGluingNativeDerivedNormalizationCube_shared_face :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 _)) ≫
        dgGluingNativeDerivedPreNormalizeCube R C D M X Y =
      (Δ[1] ◁ prismEndpoint 0 _) ≫ dgGluingNativeDerivedPostNormalizeCube R C D M X Y := by
  rw [dgGluingNativeDerivedPreNormalizeCube, dgGluingNativeDerivedPostNormalizeCube,
    ← Category.assoc, ← Category.assoc, dgGluingNativeNormalizationCube_shared_face]

end SerrePositivity.InfinityCategories
