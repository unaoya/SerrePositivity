module
public import SerrePositivity.InfinityCategories.Derived.Gluing.OrdinaryPullbackStability
/-!
概要：通常 pullback の正本比較は元 gluing の両射影を厳密に回収する。
方針：通常から lax への比較包含の式を、正本比較の両射影へ合成する。
規約：射影は元の左右 dg 対象を取り出す全単体写像の制限。
使われ方：Verdier 商の二射と K-8 の元の二入力の照合に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
lemma dgGluingOrdinaryPullbackComparison_fst :
    dgGluingOrdinaryPullbackComparison R C D M ≫
      F2.catPullbackFst (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M) =
    dgGluingPullbackUniverseInclusion R C D M ≫ dgGluingUniverseLeftNerve R C D M := by
  rw [← F2.catPullbackToLax_fst, ← Category.assoc,
    dgGluingOrdinaryPullbackComparison_toLax]
  exact Category.assoc _ _ _ |>.trans
    (congrArg (dgGluingPullbackUniverseInclusion R C D M ≫ ·)
      (dgGluingUniverseDerivedNerveLaxComparison_fst R C D M))
lemma dgGluingOrdinaryPullbackComparison_snd :
    dgGluingOrdinaryPullbackComparison R C D M ≫
      F2.catPullbackSnd (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (dgGluingUniverseDerivedCoefficient R C D M) =
    dgGluingPullbackUniverseInclusion R C D M ≫ dgGluingUniverseRightNerve R C D M := by
  rw [← F2.catPullbackToLax_snd, ← Category.assoc,
    dgGluingOrdinaryPullbackComparison_toLax]
  exact Category.assoc _ _ _ |>.trans
    (congrArg (dgGluingPullbackUniverseInclusion R C D M ≫ ·)
      (dgGluingUniverseDerivedNerveLaxComparison_snd R C D M))
variable [Small.{u} D] (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
def dgGluingPullbackStableLeftProjection :
    ExactMap (dgGluingPullbackStableObject R C D M hC hD)
      (dgGluingStableInput.{u, v, w} R C hC) :=
  ⟨dgGluingPullbackUniverseInclusion R C D M ≫ dgGluingUniverseLeftNerve R C D M, by
    let := dgGluingPullbackUniverseInclusion_isExactFunctor R C D M hC hD
    let := dgGluingUniverseLeftNerve_isExactFunctor R C D M hC hD
    exact isExactFunctor_comp _ _⟩
def dgGluingPullbackStableRightProjection :
    ExactMap (dgGluingPullbackStableObject R C D M hC hD)
      (dgGluingStableInput.{u, w, v} R D hD) :=
  ⟨dgGluingPullbackUniverseInclusion R C D M ≫ dgGluingUniverseRightNerve R C D M, by
    let := dgGluingPullbackUniverseInclusion_isExactFunctor R C D M hC hD
    let := dgGluingUniverseRightNerve_isExactFunctor R C D M hC hD
    exact isExactFunctor_comp _ _⟩
end SerrePositivity.InfinityCategories
