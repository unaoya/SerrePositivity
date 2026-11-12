module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyLeft
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyUnit
public import SerrePositivity.KST.SConstruction.PointedEnrichedSpanFunctor
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.StrictSimplicialTransformationWhisker

/-! # 元の Kan 隣接段 span 全体への厳密 dg 豊穣関手
概要：同じ三つの値と左右の前向き実射を、全 span の標準 end に豊穣に束ねる。
方針：左右の厳密自然変換の元の成分を回収し、全 Hom の前後合成で end へ持ち上げる。
規約：自然な逆・単射性・BF 条件は仮定しない。使われ方：関手的 BF 置換の実入力。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の左脚は、全厳密 dg 入力 Hom の前後合成に厳密に自然。 -/
lemma presentedPerfectDGKanAssemblyLeft_whisker (r : ℕ) (C D : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblySourceFunctor A r).map C D ≫
      eHomWhiskerLeft SSet ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C)
        (presentedPerfectDGKanAssemblyLeftMap A r D) =
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r).map C D ≫
      eHomWhiskerRight SSet (presentedPerfectDGKanAssemblyLeftMap A r C)
        ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj D) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformation_whisker _ _
    (presentedPerfectDGKanAssemblyLeftTransformation A r) (presentedPerfectDGKanAssemblyLeftMap A r)
    (presentedPerfectDGKanAssemblyLeftTransformation_app A r) C D

/-- 元の右脚も、全厳密 dg 入力 Hom の前後合成に厳密に自然。 -/
lemma presentedPerfectDGKanAssemblyRight_whisker (r : ℕ) (C D : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblySourceFunctor A r).map C D ≫
      eHomWhiskerLeft SSet ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C)
        (presentedPerfectDGKanAssemblyRightMap A r D) =
    (presentedPerfectDGKanAssemblyTargetFunctor A r).map C D ≫
      eHomWhiskerRight SSet (presentedPerfectDGKanAssemblyRightMap A r C)
        ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj D) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformation_whisker _ _
    (presentedPerfectDGKanAssemblyRightTransformation A r)
    (presentedPerfectDGKanAssemblyRightMap A r)
    (presentedPerfectDGKanAssemblyRightTransformation_app A r) C D

/-- 元の隣接段 span 図式全体へ送る、全 native Hom を保持した厳密豊穣関手。 -/
def presentedPerfectDGKanAssemblySpanEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSpanDiagram.{max (u + 1) v} :=
  pointedEnrichedSpanFunctor
    (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r)
    (presentedPerfectDGKanAssemblyTargetFunctor A r)
    (presentedPerfectDGKanAssemblyLeftMap A r) (presentedPerfectDGKanAssemblyRightMap A r)
    (presentedPerfectDGKanAssemblyLeft_whisker A r) (presentedPerfectDGKanAssemblyRight_whisker A r)

/-- 実値は、同じ元の左脚と右脚からなる実際の WalkingSpan 図式。 -/
lemma presentedPerfectDGKanAssemblySpanEnrichedFunctor_obj (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGKanAssemblySpanEnrichedFunctor A r).obj C).diagram =
      span (presentedPerfectDGKanAssemblyLeftMap A r C)
        (presentedPerfectDGKanAssemblyRightMap A r C) := rfl

/-- 全 span の Hom の射影は、各頂点の元の全厳密 dg パラメータ作用を回収する。 -/
lemma presentedPerfectDGKanAssemblySpanEnrichedFunctor_projection (r : ℕ)
    (C D : PerfDGInput.{u, v} A) (i : WalkingSpan) :
    (presentedPerfectDGKanAssemblySpanEnrichedFunctor A r).map C D ≫
      pointedSpanProjection ((presentedPerfectDGKanAssemblySpanEnrichedFunctor A r).obj C)
        ((presentedPerfectDGKanAssemblySpanEnrichedFunctor A r).obj D) i =
    pointedEnrichedSpanComponentMap
      (presentedPerfectDGKanAssemblySourceFunctor A r)
      (presentedPerfectDGKanAssemblyLeftTargetFunctor A r)
      (presentedPerfectDGKanAssemblyTargetFunctor A r)
      (presentedPerfectDGKanAssemblyLeftMap A r)
      (presentedPerfectDGKanAssemblyRightMap A r) C D i :=
  pointedEnrichedSpanHom_projection _ _ _ _ _
    (presentedPerfectDGKanAssemblyLeft_whisker A r)
    (presentedPerfectDGKanAssemblyRight_whisker A r) C D i

end SerrePositivity.KST.SConstruction
