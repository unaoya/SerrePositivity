module
public import SerrePositivity.KST.SConstruction.StableSuspensionAssemblyTransformation
public import SerrePositivity.KST.SConstruction.StableOneDirectionPointedComparison
public import SerrePositivity.KST.SConstruction.ExInfinityThenSuspensionHom
public import SerrePositivity.KST.SConstruction.ExInfinitySuspensionTransformation
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.StrictSimplicialTransformationPrecompose
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.StrictSimplicialTransformationReassociate
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.StrictSimplicialTransformationComposition
public import SerrePositivity.KST.SConstruction.StrictSimplicialTransformationComponent

/-!
概要：元の隣接段 span の両脚を同じ Ex∞ と全自然同値族で保持する。
方針：元の S₁ 比較と組み立て変換を同じ suspension 比較へ合成する。
規約：段の比較 span のみを構成する。使われ方：有限 native BF 再帰への制限。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet InfinityCategories LocalizingInvariants

/-- 概要：同じ一次方向 Kan 商の suspension。
方針：同じ Ex∞ の後に元の suspension を取る。
規約：全 Hom を保つ。使われ方：隣接段 span の源。 -/
def stableKanAssemblySourceFunctor (r : ℕ) :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} PointedSSetObject.{u} :=
  (stableOneDirectionPointedEnrichedFunctor r).comp SSet
    (coaugmentedThenSuspensionFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit)

/-- 概要：同じ境界 Kan 商の suspension。
方針：同じ元の境界商関手へ同じ Ex∞ と suspension を合成する。
規約：比較の逆は選ばない。使われ方：span の左標的。 -/
def stableKanAssemblyLeftTargetFunctor (r : ℕ) :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} PointedSSetObject.{u} :=
  (stableBoundaryPointedEnrichedFunctor r).comp SSet
    (coaugmentedThenSuspensionFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit)

/-- 概要：元の一次方向商の suspension の Ex∞ 像。
方針：元の順の二関手を合成する。
規約：同じ円と単位を保つ。使われ方：span 右脚の中間値。 -/
def stableKanAssemblyMiddleFunctor (r : ℕ) :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} PointedSSetObject.{u} :=
  (stableOneDirectionPointedEnrichedFunctor r).comp SSet
    (suspensionThenCoaugmentedFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit)

/-- 概要：同じ隣接境界商の Ex∞ 値。
方針：同じ元の境界商へ Ex∞ を後合成する。
規約：元の正段を保持。使われ方：span の右標的。 -/
def stableKanAssemblyTargetFunctor (r : ℕ) :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} PointedSSetObject.{u} :=
  (stableBoundaryPointedEnrichedFunctor (r + 1)).comp SSet exInfinityPointedEnrichedFunctor

/-- 概要：同じ Kan S₁ 比較の suspension による全族左脚。
方針：元の S₁ 変換へ同じ二関手を後合成する。
規約：元の全高次入力を保つ。使われ方：有限 BF 帰納の前向き比較。 -/
def stableKanAssemblyLeftTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (stableKanAssemblySourceFunctor r) (stableKanAssemblyLeftTargetFunctor r) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationPostcompose _ _
    (coaugmentedThenSuspensionFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit)
    (stableOneDirectionPointedComparison r)

/-- 概要：同じ元の Ex∞ suspension 比較の全族変換。
方針：元の一次方向商関手で前合成する。
規約：比較の逆なし。使われ方：span 右脚の前半。 -/
def stableKanAssemblySigmaTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (stableKanAssemblySourceFunctor r) (stableKanAssemblyMiddleFunctor r) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationPrecompose (stableOneDirectionPointedEnrichedFunctor r)
    _ _ exInfinitySuspensionTransformation

/-- 概要：同じ元の組み立ての Ex∞ 全族変換。
方針：同じ変換を後合成し、元の三関手の括弧を同じ成分のまま合わせる。
規約：元の実組み立てを保つ。使われ方：span 右脚の後半。 -/
def stableKanAssemblyExTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (stableKanAssemblyMiddleFunctor r) (stableKanAssemblyTargetFunctor r) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationReassociateSource (stableOneDirectionPointedEnrichedFunctor r)
    pointedSSetSuspensionEnrichedFunctor exInfinityPointedEnrichedFunctor _
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationPostcompose _ _ exInfinityPointedEnrichedFunctor
      (stableSuspensionAssemblyTransformation r))

/-- 概要：同じ比較と元の組み立ての像からなる全族右脚。
方針：元の二つの全族変換を合成する。
規約：全 Hom と同じ成分を保つ。使われ方：有限 BF 次段の入力。 -/
def stableKanAssemblyRightTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (stableKanAssemblySourceFunctor r) (stableKanAssemblyTargetFunctor r) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationComp _ _ _ (stableKanAssemblySigmaTransformation r)
    (stableKanAssemblyExTransformation r)

/-- 概要：同じ全族左脚の実点つき成分。
方針：厳密豊穣変換の同じ Hom 成分を回収する。
規約：元の実成分を固定。使われ方：有限 BF 次段の左脚。 -/
def stableKanAssemblyLeftMap (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableKanAssemblySourceFunctor r).obj C ⟶
      (stableKanAssemblyLeftTargetFunctor r).obj C :=
  exInfinityThenSuspensionMap (stableOneDirectionPointedComparisonMap r C)

/-- 概要：同じ全族右脚の実点つき成分。
方針：厳密豊穣変換の同じ Hom 成分を回収する。
規約：元の実成分を固定。使われ方：有限 BF 次段の右脚。 -/
def stableKanAssemblyRightMap (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableKanAssemblySourceFunctor r).obj C ⟶ (stableKanAssemblyTargetFunctor r).obj C :=
  exInfinitySuspensionComparison ((stableOneDirectionPointedEnrichedFunctor r).obj C) ≫
    coaugmentedPointedMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
      (stableSuspensionAssemblyMap r C)

end SerrePositivity.KST.SConstruction
