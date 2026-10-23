module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeIdentityComma
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationCubeIntervalFaces

/-! 加群恒等 comma の実正規化 cube を、元の加群 nerve 上へ戻す。元 D の宇宙を制限しない。 -/
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

def dgGluingNativePreNormalizeRawCube :
    (Δ[1] : SSet.{max (u + 1) v}) ⊗ (Δ[1] ⊗ (Δ[1] ⊗ DGNerve.pinchedHom R Q IX IY)) ⟶
      dgNerve R E :=
  dgGluingIdentityCommaPreNormalizeCube R E IX IY (𝟙 _) ≫
    dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)

def dgGluingNativePostNormalizeRawCube :
    (Δ[1] : SSet.{max (u + 1) v}) ⊗ (Δ[1] ⊗ (Δ[1] ⊗ DGNerve.pinchedHom R Q IX IY)) ⟶
      dgNerve R E :=
  dgGluingIdentityCommaPostNormalizeCube R E IX IY (𝟙 _) ≫
    dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E)

end SerrePositivity.InfinityCategories
