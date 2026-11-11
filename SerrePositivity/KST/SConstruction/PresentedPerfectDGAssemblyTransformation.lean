module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGSuspensionAssemblyAction
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionPointedFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBoundaryPointedFunctor
public import SerrePositivity.KST.SConstruction.PointedSSetSuspensionFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGAssemblyFamilies
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.StrictSimplicialTransformation

/-! # 元の suspension 組み立ての厳密単体的自然変換
概要：元の同じ組み立てを、全厳密 dg 入力上の点つき豊穣自然変換へ束ねる。
方針：元の全 basedHom 族自然性を、標準点つき豊穣の前後合成で読む。
規約：元の円・商・組み立てを変更しない。使われ方：Kan 後の隣接段 span の右脚。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の一次方向商を同じ円で suspension した、全 dg 入力上の厳密豊穣関手。 -/
def presentedPerfectDGAssemblySourceFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSSetObject.{max (u + 1) v} :=
  (presentedPerfectDGOneDirectionPointedEnrichedFunctor.{u, v} A r).comp SSet
    pointedSSetSuspensionEnrichedFunctor

/-- 標準点つき値の間の、元の同じ suspension 組み立て。 -/
def presentedPerfectDGAssemblyMap (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGAssemblySourceFunctor.{u, v} A r).obj C ⟶
      (presentedPerfectDGBoundaryPointedEnrichedFunctor.{u, v} A (r + 1)).obj C :=
  oneDirectionSuspensionAssembly r
    (stableCategoryModel (presentedPerfectDGStableCategory.{u, v} A C))

/-- 同じ元の組み立てを全 native Hom 上で束ねた、厳密単体的自然変換。 -/
def presentedPerfectDGAssemblyTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      (presentedPerfectDGAssemblySourceFunctor.{u, v} A r)
      (presentedPerfectDGBoundaryPointedEnrichedFunctor.{u, v} A (r + 1)) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _
    (presentedPerfectDGAssemblyMap.{u, v} A r)
    (presentedPerfectDGAssemblyFamily_whisker.{u, v} A r)

/-- 厳密自然変換の成分は、元の同じ suspension 組み立ての豊穣表示。 -/
lemma presentedPerfectDGAssemblyTransformation_app (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGAssemblyTransformation.{u, v} A r).app C =
      eHomEquiv SSet (presentedPerfectDGAssemblyMap.{u, v} A r C) := rfl

end SerrePositivity.KST.SConstruction
