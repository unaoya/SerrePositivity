module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyCylinderComparisons
public import SerrePositivity.KST.SConstruction.PointedEnrichedMappingCylinderTransformations

/-! # 元の隣接段実写像円柱比較の厳密 dg 自然変換
概要：同じ源比較・標的包含・射影を、全厳密 dg 入力の豊穣自然変換へ束ねる。
方針：元の全 Hom 自然な左脚に、実写像円柱の厳密自然変換を適用する。
規約：元の同じ実成分を回収。使われ方：BF の関手的置換と元の span の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の隣接段源から同じ実写像円柱への厳密豊穣自然変換。 -/
def presentedPerfectDGKanAssemblyCylinderSourceTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      (presentedPerfectDGKanAssemblySourceFunctor A r)
      (presentedPerfectDGKanAssemblyLeftCylinderFunctor A r) :=
  pointedEnrichedMappingCylinderSourceTransformation
    (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r)
    (presentedPerfectDGKanAssemblyLeftMap A r) (presentedPerfectDGKanAssemblyLeft_whisker A r)

/-- 元の隣接段左標的から同じ実写像円柱への厳密豊穣自然変換。 -/
def presentedPerfectDGKanAssemblyCylinderTargetTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      (presentedPerfectDGKanAssemblyLeftTargetFunctor A r)
      (presentedPerfectDGKanAssemblyLeftCylinderFunctor A r) :=
  pointedEnrichedMappingCylinderTargetTransformation
    (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r)
    (presentedPerfectDGKanAssemblyLeftMap A r) (presentedPerfectDGKanAssemblyLeft_whisker A r)

/-- 同じ実写像円柱から元の隣接段左標的への厳密豊穣射影。 -/
def presentedPerfectDGKanAssemblyCylinderProjectionTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      (presentedPerfectDGKanAssemblyLeftCylinderFunctor A r)
      (presentedPerfectDGKanAssemblyLeftTargetFunctor A r) :=
  pointedEnrichedMappingCylinderProjectionTransformation
    (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r)
    (presentedPerfectDGKanAssemblyLeftMap A r) (presentedPerfectDGKanAssemblyLeft_whisker A r)

/-- 源比較の豊穣成分は、同じ元の実写像円柱源射を回収する。 -/
lemma presentedPerfectDGKanAssemblyCylinderSourceTransformation_app (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyCylinderSourceTransformation A r).app C =
      eHomEquiv SSet (presentedPerfectDGKanAssemblyCylinderSourceMap A r C) := rfl

/-- 標的包含の豊穣成分は、同じ元の実写像円柱標的射を回収する。 -/
lemma presentedPerfectDGKanAssemblyCylinderTargetTransformation_app (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyCylinderTargetTransformation A r).app C =
      eHomEquiv SSet (presentedPerfectDGKanAssemblyCylinderTargetMap A r C) := rfl

/-- 豊穣射影の成分は、同じ元の実写像円柱射影を回収する。 -/
lemma presentedPerfectDGKanAssemblyCylinderProjectionTransformation_app (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyCylinderProjectionTransformation A r).app C =
      eHomEquiv SSet (presentedPerfectDGKanAssemblyCylinderProjectionMap A r C) := rfl

end SerrePositivity.KST.SConstruction
