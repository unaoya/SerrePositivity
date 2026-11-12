module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionPointedFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBoundaryPointedFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionReducedComparison
public import SerrePositivity.KST.SConstruction.PointedSSetWhisker
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.StrictSimplicialTransformation

/-! # 元の S₁ 境界商比較の厳密単体的自然変換
概要：同じ前向きの境界商比較を、全 native dg 入力上の厳密豊穣自然変換へ束ねる。
方針：元の全 basedHom 族自然性を標準点つき豊穣の前後合成で読む。
規約：逆射は選ばない。使われ方：同じ Ex∞ 後の隣接段比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 二つの標準点つき値の間の、同じ元の前向き S₁ 商比較。 -/
def presentedPerfectDGOneDirectionPointedComparisonMap (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj C ⟶
      (presentedPerfectDGBoundaryPointedEnrichedFunctor A r).obj C :=
  oneDirectionReducedComparison r (stableCategoryModel (presentedPerfectDGStableCategory A C))

/-- 元の全族自然性は、標準点つき豊穣の全 Hom の前後合成とも厳密に可換。 -/
lemma presentedPerfectDGOneDirectionPointedComparison_whisker (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    (presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).map C D ≫
      eHomWhiskerLeft SSet
        ((presentedPerfectDGOneDirectionPointedEnrichedFunctor A r).obj C)
        (presentedPerfectDGOneDirectionPointedComparisonMap A r D) =
    (presentedPerfectDGBoundaryPointedEnrichedFunctor A r).map C D ≫
      eHomWhiskerRight SSet (presentedPerfectDGOneDirectionPointedComparisonMap A r C)
        ((presentedPerfectDGBoundaryPointedEnrichedFunctor A r).obj D) := by
  rw [pointedSSetObject_whiskerLeft, pointedSSetObject_whiskerRight]
  exact presentedPerfectDGOneDirectionReducedComparison_family A r C D

/-- 元の S₁ 商比較を全 native 入力上で束ねた、標準点つき厳密豊穣自然変換。 -/
def presentedPerfectDGOneDirectionPointedComparison (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      (presentedPerfectDGOneDirectionPointedEnrichedFunctor A r)
      (presentedPerfectDGBoundaryPointedEnrichedFunctor A r) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _
    (presentedPerfectDGOneDirectionPointedComparisonMap A r)
    (presentedPerfectDGOneDirectionPointedComparison_whisker A r)

/-- 厳密豊穣自然変換の成分は、同じ元の S₁ 商比較の標準豊穣表示。 -/
lemma presentedPerfectDGOneDirectionPointedComparison_app (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGOneDirectionPointedComparison A r).app C =
      eHomEquiv SSet (presentedPerfectDGOneDirectionPointedComparisonMap A r C) := rfl

end SerrePositivity.KST.SConstruction
