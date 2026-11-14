module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.LaxComparisonStability
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategories
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
/-- 概要：元の入力 nerve を共通宇宙の安定圏に束ねる。
方針：前三角性から安定性を得る。規約：全単体を保持する。使われ方：二つの入力圏。 -/
def dgGluingStableInput (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{max (u + 1) v w} where
  obj := (SSet.uliftFunctor.{max (u + 1) v w,max u v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)
  isQuasicategory := inferInstance
  isStable := by
    let := hC
    let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R C
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Idempotent.isStable_ulift
variable (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
  (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
def dgGluingStableObject : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{max (u + 1) v w} where
  obj := (SSet.uliftFunctor.{max (u + 1) v w,max u v w}).obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M))
  isQuasicategory := inferInstance
  isStable := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerve_isStable R C D M hC hD
def dgGluingStableLaxObject : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{max (u + 1) v w} where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u,v,w} R C)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M)
  isQuasicategory := inferInstance
  isStable := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedLaxPullback_isStable R C D M hC hD
def dgGluingStableLeftProjection : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgGluingStableObject R C D M hC hD)
    (dgGluingStableInput.{u,v,w} R C hC) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseLeftNerve R C D M,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseLeftNerve_isExactFunctor R C D M hC hD⟩
def dgGluingStableRightProjection : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgGluingStableObject R C D M hC hD)
    (dgGluingStableInput.{u,w,v} R D hD) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseRightNerve R C D M,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseRightNerve_isExactFunctor R C D M hC hD⟩
def dgGluingStableComparison : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgGluingStableObject R C D M hC hD)
    (dgGluingStableLaxObject R C D M hC hD) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R C D M,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_isExactFunctor R C D M⟩
def dgGluingStableLaxFst : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgGluingStableLaxObject R C D M hC hD)
    (dgGluingStableInput.{u,v,w} R C hC) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u,v,w} R C)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedLaxPullbackFst_isExactFunctor R C D M hC hD⟩
def dgGluingStableLaxSnd : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgGluingStableLaxObject R C D M hC hD)
    (dgGluingStableInput.{u,w,v} R D hD) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u,v,w} R C)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedLaxPullbackSnd_isExactFunctor R C D M hC hD⟩
lemma dgGluingStableComparison_fst :
    (show dgGluingStableObject R C D M hC hD ⟶ dgGluingStableLaxObject R C D M hC hD
      from dgGluingStableComparison R C D M hC hD) ≫ dgGluingStableLaxFst R C D M hC hD =
      dgGluingStableLeftProjection R C D M hC hD :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_fst R C D M)
lemma dgGluingStableComparison_snd :
    (show dgGluingStableObject R C D M hC hD ⟶ dgGluingStableLaxObject R C D M hC hD
      from dgGluingStableComparison R C D M hC hD) ≫ dgGluingStableLaxSnd R C D M hC hD =
      dgGluingStableRightProjection R C D M hC hD :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_snd R C D M)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
