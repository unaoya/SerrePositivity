module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxComparisonStability
public import SerrePositivity.InfinityCategories.Stable.Verdier.StableCategories
/-!
概要：元 dg gluing と正本 lax pullback を、K-8 の同じ宇宙の安定圏として束ねる。
方針：実 nerve・宇宙持ち上げ・左右射影・比較の完全性だけを束ねる。
規約：対象や関手を別の完備化へ置換しない。
使われ方：K-8b の半直交分解と gluing の比較、Verdier 列の具体的入力に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
/-- 概要：元の入力 nerve を共通宇宙の安定圏に束ねる。
方針：前三角性から安定性を得る。規約：全単体を保持する。使われ方：二つの入力圏。 -/
def dgGluingStableInput (hC : IsDGPretriangulated R C) :
    _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{max (u + 1) v w} where
  obj := (SSet.uliftFunctor.{max (u + 1) v w,max u v}).obj (dgNerve R C)
  isQuasicategory := inferInstance
  isStable := by
    let := hC
    let := dgNerve_isStable_of_pretriangulated R C
    exact F2.Idempotent.isStable_ulift
variable (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
def dgGluingStableObject : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{max (u + 1) v w} where
  obj := (SSet.uliftFunctor.{max (u + 1) v w,max u v w}).obj
    (dgNerve R (DGGluingObject R C D M))
  isQuasicategory := inferInstance
  isStable := dgGluingUniverseNerve_isStable R C D M hC hD
def dgGluingStableLaxObject : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{max (u + 1) v w} where
  obj := F2.laxPullback (dgGluingUniverseDerivedYoneda.{u,v,w} R C)
    (dgGluingUniverseDerivedCoefficient R C D M)
  isQuasicategory := inferInstance
  isStable := dgGluingUniverseDerivedLaxPullback_isStable R C D M hC hD
def dgGluingStableLeftProjection : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (dgGluingStableObject R C D M hC hD)
    (dgGluingStableInput.{u,v,w} R C hC) :=
  ⟨dgGluingUniverseLeftNerve R C D M,
    dgGluingUniverseLeftNerve_isExactFunctor R C D M hC hD⟩
def dgGluingStableRightProjection : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (dgGluingStableObject R C D M hC hD)
    (dgGluingStableInput.{u,w,v} R D hD) :=
  ⟨dgGluingUniverseRightNerve R C D M,
    dgGluingUniverseRightNerve_isExactFunctor R C D M hC hD⟩
def dgGluingStableComparison : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (dgGluingStableObject R C D M hC hD)
    (dgGluingStableLaxObject R C D M hC hD) :=
  ⟨dgGluingUniverseDerivedNerveLaxComparison R C D M,
    dgGluingUniverseDerivedNerveLaxComparison_isExactFunctor R C D M⟩
def dgGluingStableLaxFst : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (dgGluingStableLaxObject R C D M hC hD)
    (dgGluingStableInput.{u,v,w} R C hC) :=
  ⟨F2.laxPullbackFst (dgGluingUniverseDerivedYoneda.{u,v,w} R C)
    (dgGluingUniverseDerivedCoefficient R C D M),
    dgGluingUniverseDerivedLaxPullbackFst_isExactFunctor R C D M hC hD⟩
def dgGluingStableLaxSnd : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (dgGluingStableLaxObject R C D M hC hD)
    (dgGluingStableInput.{u,w,v} R D hD) :=
  ⟨F2.laxPullbackSnd (dgGluingUniverseDerivedYoneda.{u,v,w} R C)
    (dgGluingUniverseDerivedCoefficient R C D M),
    dgGluingUniverseDerivedLaxPullbackSnd_isExactFunctor R C D M hC hD⟩
lemma dgGluingStableComparison_fst :
    (show dgGluingStableObject R C D M hC hD ⟶ dgGluingStableLaxObject R C D M hC hD
      from dgGluingStableComparison R C D M hC hD) ≫ dgGluingStableLaxFst R C D M hC hD =
      dgGluingStableLeftProjection R C D M hC hD :=
  _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.ext (dgGluingUniverseDerivedNerveLaxComparison_fst R C D M)
lemma dgGluingStableComparison_snd :
    (show dgGluingStableObject R C D M hC hD ⟶ dgGluingStableLaxObject R C D M hC hD
      from dgGluingStableComparison R C D M hC hD) ≫ dgGluingStableLaxSnd R C D M hC hD =
      dgGluingStableRightProjection R C D M hC hD :=
  _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.ext (dgGluingUniverseDerivedNerveLaxComparison_snd R C D M)
end SerrePositivity.InfinityCategories
