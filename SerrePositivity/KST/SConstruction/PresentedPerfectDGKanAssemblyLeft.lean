module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGAssemblyExInfinity
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionKanComparison
public import SerrePositivity.KST.SConstruction.ExInfinityThenSuspensionHom

/-! # 元の Kan S₁ 比較の suspension による隣接段 span の左脚
概要：ΣEx∞U_r から ΣEx∞B_r への同じ前向き比較を全 dg 入力に厳密に自然に束ねる。
方針：元の S₁ 比較を同じ Ex∞ と元の円の suspension で後合成する。
規約：自然な逆は選ばない。使われ方：BF 置換の前向き span。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ境界商の Ex∞ Kan 値の suspension を与える厳密豊穣関手。 -/
def presentedPerfectDGKanAssemblyLeftTargetFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSSetObject.{max (u + 1) v} :=
  (presentedPerfectDGBoundaryPointedEnrichedFunctor A r).comp SSet
    (coaugmentedThenSuspensionFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit)

/-- 元の Kan S₁ 比較の同じ suspension による、実際の前向き左脚。 -/
def presentedPerfectDGKanAssemblyLeftMap (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblySourceFunctor A r).obj C ⟶
      (presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C :=
  exInfinityThenSuspensionMap (presentedPerfectDGOneDirectionPointedComparisonMap A r C)

/-- 左脚の元の全 Hom を保持する、厳密単体的自然変換。 -/
def presentedPerfectDGKanAssemblyLeftTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      (presentedPerfectDGKanAssemblySourceFunctor A r)
      (presentedPerfectDGKanAssemblyLeftTargetFunctor A r) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationPostcompose _ _
    (coaugmentedThenSuspensionFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit)
    (presentedPerfectDGOneDirectionPointedComparison A r)

/-- 厳密自然変換の成分は、元の同じ Kan 比較の suspension そのもの。 -/
lemma presentedPerfectDGKanAssemblyLeftTransformation_app (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyLeftTransformation A r).app C =
      eHomEquiv SSet (presentedPerfectDGKanAssemblyLeftMap A r C) :=
  exInfinityThenSuspensionFunctor_hom (presentedPerfectDGOneDirectionPointedComparisonMap A r C)

/-- 左脚は、元の同じ Kan S₁ 比較の基点固定の suspension 射。 -/
lemma presentedPerfectDGKanAssemblyLeftMap_eq (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyLeftMap A r C) =
      PointedSimplicialSet.circle.{max (u + 1) v} ◁
        (presentedPerfectDGOneDirectionKanComparisonMap A r C).hom := rfl

end SerrePositivity.KST.SConstruction
