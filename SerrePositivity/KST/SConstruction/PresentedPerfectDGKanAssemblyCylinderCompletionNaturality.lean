module
public import
  SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyCylinderPushoutCompletion

/-! # 同じ Ex∞ 円柱押し出し比較の全 Hom 自然性
概要：元の単位と両標的比較は、同じ Kan 候補への厳密豊穣自然変換をなす。
方針：同じ単位の全 Hom 自然性を元の両比較と合成する。
規約：通常の成分も全高次入力も保持。使われ方：BF 帰納段の前向き比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ元の実押し出しから Kan 候補への単位は、全 Hom に自然。 -/
lemma presentedPerfectDGKanAssemblyCylinderCompletionUnit_whisker (r : ℕ)
    (X Y : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).map X Y ≫
        eHomWhiskerLeft SSet ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj X)
          (presentedPerfectDGKanAssemblyCylinderCompletionUnit A r Y) =
      (presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).map X Y ≫
        eHomWhiskerRight SSet (presentedPerfectDGKanAssemblyCylinderCompletionUnit A r X)
          ((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj Y) :=
  enrichedExInfinityPointedUnit_whisker
    (presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r) X Y

/-- 元の左標的から同じ Kan 候補への比較は、全 Hom に自然。 -/
lemma presentedPerfectDGKanAssemblyCylinderCompletionLeft_whisker (r : ℕ)
    (X Y : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r).map X Y ≫
        eHomWhiskerLeft SSet ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj X)
          (presentedPerfectDGKanAssemblyCylinderCompletionLeftMap A r Y) =
      (presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).map X Y ≫
        eHomWhiskerRight SSet (presentedPerfectDGKanAssemblyCylinderCompletionLeftMap A r X)
          ((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj Y) :=
  enriched_whisker_naturality_comp SSet
    ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).map X Y)
    ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).map X Y)
    ((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).map X Y)
    (presentedPerfectDGKanAssemblyCylinderPushoutLeftMap A r X)
    (presentedPerfectDGKanAssemblyCylinderPushoutLeftMap A r Y)
    (presentedPerfectDGKanAssemblyCylinderCompletionUnit A r X)
    (presentedPerfectDGKanAssemblyCylinderCompletionUnit A r Y)
    (presentedPerfectDGKanAssemblyCylinderPushoutLeft_whisker A r X Y)
    (presentedPerfectDGKanAssemblyCylinderCompletionUnit_whisker A r X Y)

/-- 元の右標的から同じ Kan 候補への比較は、全 Hom に自然。 -/
lemma presentedPerfectDGKanAssemblyCylinderCompletionRight_whisker (r : ℕ)
    (X Y : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyTargetFunctor A r).map X Y ≫
        eHomWhiskerLeft SSet ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj X)
          (presentedPerfectDGKanAssemblyCylinderCompletionRightMap A r Y) =
      (presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).map X Y ≫
        eHomWhiskerRight SSet (presentedPerfectDGKanAssemblyCylinderCompletionRightMap A r X)
          ((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj Y) :=
  enriched_whisker_naturality_comp SSet
    ((presentedPerfectDGKanAssemblyTargetFunctor A r).map X Y)
    ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).map X Y)
    ((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).map X Y)
    (presentedPerfectDGKanAssemblyCylinderPushoutRightMap A r X)
    (presentedPerfectDGKanAssemblyCylinderPushoutRightMap A r Y)
    (presentedPerfectDGKanAssemblyCylinderCompletionUnit A r X)
    (presentedPerfectDGKanAssemblyCylinderCompletionUnit A r Y)
    (presentedPerfectDGKanAssemblyCylinderPushoutRight_whisker A r X Y)
    (presentedPerfectDGKanAssemblyCylinderCompletionUnit_whisker A r X Y)

/-- 同じ Unit 比較を成分とする厳密豊穣自然変換。 -/
def presentedPerfectDGKanAssemblyCylinderCompletionUnitTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      (presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r)
      (presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _
    (presentedPerfectDGKanAssemblyCylinderCompletionUnit A r)
    (presentedPerfectDGKanAssemblyCylinderCompletionUnit_whisker A r)

/-- 豊穣変換の成分は同じ元の Unit 比較。 -/
lemma presentedPerfectDGKanAssemblyCylinderCompletionUnitTransformation_app (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyCylinderCompletionUnitTransformation A r).app C =
      eHomEquiv SSet (presentedPerfectDGKanAssemblyCylinderCompletionUnit A r C) := rfl

/-- 同じ Left 比較を成分とする厳密豊穣自然変換。 -/
def presentedPerfectDGKanAssemblyCylinderCompletionLeftTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      (presentedPerfectDGKanAssemblyLeftTargetFunctor A r)
      (presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _
    (presentedPerfectDGKanAssemblyCylinderCompletionLeftMap A r)
    (presentedPerfectDGKanAssemblyCylinderCompletionLeft_whisker A r)

/-- 豊穣変換の成分は同じ元の Left 比較。 -/
lemma presentedPerfectDGKanAssemblyCylinderCompletionLeftTransformation_app (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyCylinderCompletionLeftTransformation A r).app C =
      eHomEquiv SSet (presentedPerfectDGKanAssemblyCylinderCompletionLeftMap A r C) := rfl

/-- 同じ Right 比較を成分とする厳密豊穣自然変換。 -/
def presentedPerfectDGKanAssemblyCylinderCompletionRightTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      (presentedPerfectDGKanAssemblyTargetFunctor A r)
      (presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _
    (presentedPerfectDGKanAssemblyCylinderCompletionRightMap A r)
    (presentedPerfectDGKanAssemblyCylinderCompletionRight_whisker A r)

/-- 豊穣変換の成分は同じ元の Right 比較。 -/
lemma presentedPerfectDGKanAssemblyCylinderCompletionRightTransformation_app (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyCylinderCompletionRightTransformation A r).app C =
      eHomEquiv SSet (presentedPerfectDGKanAssemblyCylinderCompletionRightMap A r C) := rfl

end SerrePositivity.KST.SConstruction
