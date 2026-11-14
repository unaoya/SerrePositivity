module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGAssemblyExInfinity
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.StrictSimplicialTransformationComposition

/-! # 元の Ex∞ 比較と組み立てを合成した隣接段の右脚
概要：ΣEx∞U_r から同じ元の Ex∞B_(r+1) への実射を全 dg 入力に自然に束ねる。
方針：元の suspension 比較と同じ組み立ての Ex∞ 像を、全 Hom 上で厳密に合成する。
規約：比較の逆・単射性は要求しない。使われ方：BF 置換へ渡す前向き span。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 一次方向の同じ商に対する、元の Ex∞ suspension 比較の実成分。 -/
def presentedPerfectDGKanAssemblySigmaMap (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblySourceFunctor A r).obj C ⟶
      (presentedPerfectDGKanAssemblyMiddleFunctor A r).obj C :=
  exInfinitySuspensionComparison
    ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj C)

/-- 元の比較と元の組み立ての像からなる、同じ隣接段への実際の右脚。 -/
def presentedPerfectDGKanAssemblyRightMap (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblySourceFunctor A r).obj C ⟶
      (presentedPerfectDGKanAssemblyTargetFunctor A r).obj C :=
  presentedPerfectDGKanAssemblySigmaMap A r C ≫ presentedPerfectDGAssemblyExInfinityMap A r C

/-- 同じ右脚を全 native Hom 上で束ねた、厳密単体的自然変換。 -/
def presentedPerfectDGKanAssemblyRightTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      (presentedPerfectDGKanAssemblySourceFunctor A r)
      (presentedPerfectDGKanAssemblyTargetFunctor A r) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationComp _ _ _
    (presentedPerfectDGOneDirectionSuspensionComparison A r)
    (presentedPerfectDGAssemblyExInfinityTransformation A r)

/-- 比較側の自然変換成分は、同じ元の Ex∞ suspension 比較を回収する。 -/
lemma presentedPerfectDGKanAssemblySigmaMap_app (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGOneDirectionSuspensionComparison A r).app C =
      eHomEquiv SSet (presentedPerfectDGKanAssemblySigmaMap A r C) := rfl

/-- 合成した厳密自然変換の成分は、元の同じ二つの実射の合成そのもの。 -/
lemma presentedPerfectDGKanAssemblyRightTransformation_app (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyRightTransformation A r).app C =
      eHomEquiv SSet (presentedPerfectDGKanAssemblyRightMap A r C) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationComp_hom _ _ _ _ _ C
    (presentedPerfectDGKanAssemblySigmaMap A r C) (presentedPerfectDGAssemblyExInfinityMap A r C)
    (presentedPerfectDGKanAssemblySigmaMap_app A r C)
    (presentedPerfectDGAssemblyExInfinityTransformation_app A r C)

/-- 右脚の基礎射は、元の比較の後で同じ元の組み立てを Ex∞ で写した射。 -/
lemma presentedPerfectDGKanAssemblyRightMap_right (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyRightMap A r C).right =
    (exInfinitySuspensionComparison
      ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj C)).right ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map
        (oneDirectionSuspensionAssembly r
          (stableCategoryModel (presentedPerfectDGStableCategory A C))).right := rfl

end SerrePositivity.KST.SConstruction
