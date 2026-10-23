module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeNormalizationCubes

/-! 元の一般宇宙 gluing Hom からの実 cube は、三方向の各面を元の加群 cube の全二次元族へ戻す。 -/
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
  (V : (Δ[1] : SSet.{max (u + 1) v}) ⊗
    (Δ[1] ⊗ (Δ[1] ⊗ DGNerve.pinchedHom R
      (DGFunctorCommaObject R (RightModule R C) (RightModule R C) (DGFunctor.id (RightModule R C)))
      (dgGluingNativeIdentityCommaObject R C D M X)
      (dgGluingNativeIdentityCommaObject R C D M Y))) ⟶ dgNerve R (RightModule R C))

lemma dgGluingNativeNormalizationCube_outer (i : Fin 2) :
    prismEndpoint i _ ≫ dgGluingNativeNormalizationCube R C D M X Y V =
      (Δ[1] ◁ (Δ[1] ◁ dgGluingNativeNormalizationHomInput R C D M X Y)) ≫
        dgGluingUliftSquareFamily.{max (u + 1) v, max (u + 1) v w}
          (prismEndpoint i _ ≫ V) :=
  dgGluingUliftCubeFamily_outer_precomp V (dgGluingNativeNormalizationHomInput R C D M X Y) i

lemma dgGluingNativeNormalizationCube_middle (i : Fin 2) :
    (Δ[1] ◁ prismEndpoint i _) ≫ dgGluingNativeNormalizationCube R C D M X Y V =
      (Δ[1] ◁ (Δ[1] ◁ dgGluingNativeNormalizationHomInput R C D M X Y)) ≫
        dgGluingUliftSquareFamily.{max (u + 1) v, max (u + 1) v w}
          ((Δ[1] ◁ prismEndpoint i _) ≫ V) :=
  dgGluingUliftCubeFamily_middle_precomp V (dgGluingNativeNormalizationHomInput R C D M X Y) i

lemma dgGluingNativeNormalizationCube_inner (i : Fin 2) :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint i _)) ≫ dgGluingNativeNormalizationCube R C D M X Y V =
      (Δ[1] ◁ (Δ[1] ◁ dgGluingNativeNormalizationHomInput R C D M X Y)) ≫
        dgGluingUliftSquareFamily.{max (u + 1) v, max (u + 1) v w}
          ((Δ[1] ◁ (Δ[1] ◁ prismEndpoint i _)) ≫ V) :=
  dgGluingUliftCubeFamily_inner_precomp V (dgGluingNativeNormalizationHomInput R C D M X Y) i

end SerrePositivity.InfinityCategories
