module
public import
  SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyCylinderPushoutNaturality
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.StrictSimplicialTransformation

/-! # 同じ実円柱押し出しの両標的比較の厳密豊穣自然変換
概要：同じ左右比較を、全厳密 dg 入力に関する豊穣自然変換へ束ねる。
方針：証明済みの全 Hom 自然性を単位パラメータで表示する。
規約：元の同じ実成分を回収。使われ方：BF 帰納段の前向き比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ元の左標的から実押し出しへの厳密豊穣自然変換。 -/
def presentedPerfectDGKanAssemblyCylinderPushoutLeftTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      (presentedPerfectDGKanAssemblyLeftTargetFunctor A r)
      (presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _
    (presentedPerfectDGKanAssemblyCylinderPushoutLeftMap A r)
    (presentedPerfectDGKanAssemblyCylinderPushoutLeft_whisker A r)

/-- 豊穣変換の成分は、元の同じ実左比較。 -/
lemma presentedPerfectDGKanAssemblyCylinderPushoutLeftTransformation_app (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyCylinderPushoutLeftTransformation A r).app C =
      eHomEquiv SSet (presentedPerfectDGKanAssemblyCylinderPushoutLeftMap A r C) := rfl

/-- 同じ元の右標的から実押し出しへの厳密豊穣自然変換。 -/
def presentedPerfectDGKanAssemblyCylinderPushoutRightTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      (presentedPerfectDGKanAssemblyTargetFunctor A r)
      (presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _
    (presentedPerfectDGKanAssemblyCylinderPushoutRightMap A r)
    (presentedPerfectDGKanAssemblyCylinderPushoutRight_whisker A r)

/-- 豊穣変換の成分は、元の同じ実右比較。 -/
lemma presentedPerfectDGKanAssemblyCylinderPushoutRightTransformation_app (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyCylinderPushoutRightTransformation A r).app C =
      eHomEquiv SSet (presentedPerfectDGKanAssemblyCylinderPushoutRightMap A r C) := rfl

end SerrePositivity.KST.SConstruction
