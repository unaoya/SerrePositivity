module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationCubeBoundary
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseDerivedStructure

/-! 元 Hom からの同じ native 正規化 cube を、正本の実導来加群関手で後合成し全三方向の面を保つ。 -/
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

def dgGluingNativeDerivedPreNormalizeCube :=
  dgGluingNativePreNormalizeCube R C D M X Y ≫
    dgGluingUniverseModuleDerivedComparison.{u, v, w} R C

def dgGluingNativeDerivedPostNormalizeCube :=
  dgGluingNativePostNormalizeCube R C D M X Y ≫
    dgGluingUniverseModuleDerivedComparison.{u, v, w} R C

lemma dgGluingNativeDerivedPreNormalizeCube_inner (i : Fin 2) :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint i _)) ≫
        dgGluingNativeDerivedPreNormalizeCube R C D M X Y =
      (Δ[1] ◁ (Δ[1] ◁ dgGluingNativeNormalizationHomInput R C D M X Y)) ≫
        dgGluingUliftSquareFamily.{max (u + 1) v, max (u + 1) v w}
          ((Δ[1] ◁ (Δ[1] ◁ prismEndpoint i _)) ≫
            dgGluingNativePreNormalizeRawCube R C D M X Y) ≫
              dgGluingUniverseModuleDerivedComparison.{u, v, w} R C := by
  rw [dgGluingNativeDerivedPreNormalizeCube, ← Category.assoc, dgGluingNativePreNormalizeCube,
    dgGluingNativeNormalizationCube_inner, Category.assoc]

lemma dgGluingNativeDerivedPostNormalizeCube_inner (i : Fin 2) :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint i _)) ≫
        dgGluingNativeDerivedPostNormalizeCube R C D M X Y =
      (Δ[1] ◁ (Δ[1] ◁ dgGluingNativeNormalizationHomInput R C D M X Y)) ≫
        dgGluingUliftSquareFamily.{max (u + 1) v, max (u + 1) v w}
          ((Δ[1] ◁ (Δ[1] ◁ prismEndpoint i _)) ≫
            dgGluingNativePostNormalizeRawCube R C D M X Y) ≫
              dgGluingUniverseModuleDerivedComparison.{u, v, w} R C := by
  rw [dgGluingNativeDerivedPostNormalizeCube, ← Category.assoc, dgGluingNativePostNormalizeCube,
    dgGluingNativeNormalizationCube_inner, Category.assoc]

end SerrePositivity.InfinityCategories
