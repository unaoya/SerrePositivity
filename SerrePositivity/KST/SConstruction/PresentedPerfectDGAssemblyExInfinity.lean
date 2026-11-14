module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGAssemblyTransformation
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGSuspensionComparison
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBoundaryKanFunctor
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.StrictSimplicialTransformationReassociate

/-! # 元の suspension 組み立ての同じ Ex∞ 像
概要：元の組み立てを同じ Ex∞ で写し、比較と合成できる厳密豊穣自然変換へ束ねる。
方針：全 Hom を保つ後合成と、同じ全成分を保つ合成の括弧付けを使う。
規約：元の組み立て・基点・Kan 値は変更しない。使われ方：隣接段 span の右脚。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 一次方向の同じ Ex∞ Kan 商の suspension を与える厳密豊穣関手。 -/
def presentedPerfectDGKanAssemblySourceFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSSetObject.{max (u + 1) v} :=
  (presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).comp SSet
    (coaugmentedThenSuspensionFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit)

/-- 元の一次方向商の suspension に同じ Ex∞ を施す厳密豊穣関手。 -/
def presentedPerfectDGKanAssemblyMiddleFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSSetObject.{max (u + 1) v} :=
  (presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).comp SSet
    (suspensionThenCoaugmentedFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit)

/-- 元の隣接段の境界商の同じ Ex∞ Kan 値を与える厳密豊穣関手。 -/
def presentedPerfectDGKanAssemblyTargetFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSSetObject.{max (u + 1) v} :=
  (presentedPerfectDGBoundaryPointedEnrichedFunctor A (r + 1)).comp SSet
    exInfinityPointedEnrichedFunctor

/-- 元の同じ組み立てを同じ Ex∞ で写した、実際の点つき射。 -/
def presentedPerfectDGAssemblyExInfinityMap (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyMiddleFunctor A r).obj C ⟶
      (presentedPerfectDGKanAssemblyTargetFunctor A r).obj C :=
  coaugmentedPointedMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
    (presentedPerfectDGAssemblyMap A r C)

/-- 組み立ての Ex∞ 像を全 Hom 上で束ねた、同じ全成分の厳密自然変換。 -/
def presentedPerfectDGAssemblyExInfinityTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      (presentedPerfectDGKanAssemblyMiddleFunctor A r)
      (presentedPerfectDGKanAssemblyTargetFunctor A r) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationReassociateSource
    (presentedPerfectDGOneDirectionPointedEnrichedFunctor A r)
    pointedSSetSuspensionEnrichedFunctor exInfinityPointedEnrichedFunctor _
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationPostcompose _ _ exInfinityPointedEnrichedFunctor
      (presentedPerfectDGAssemblyTransformation A r))

/-- 厳密自然変換の成分は、元の同じ組み立ての Ex∞ 像そのもの。 -/
lemma presentedPerfectDGAssemblyExInfinityTransformation_app (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGAssemblyExInfinityTransformation A r).app C =
      eHomEquiv SSet (presentedPerfectDGAssemblyExInfinityMap A r C) :=
  coaugmentedPointedEnrichedFunctor_hom _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
    (presentedPerfectDGAssemblyMap A r C)

/-- 右脚の標的は、既存の隣接段の同じ Ex∞ Kan 境界商。 -/
lemma presentedPerfectDGKanAssemblyTargetFunctor_obj (r : ℕ) (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj =
      ((presentedPerfectDGBoundaryKanEnrichedFunctor A (r + 1)).obj C).obj := rfl

/-- 同じ標的の基礎単体集合は、元の Ex∞ による実際の Kan 値。 -/
lemma presentedPerfectDGKanAssemblyTargetFunctor_kan (r : ℕ) (C : PerfDGInput.{u, v} A) :
    KanComplex (((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj.right) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex
    (boundaryReducedRealization (r + 1)
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).right

end SerrePositivity.KST.SConstruction
