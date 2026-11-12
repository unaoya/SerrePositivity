module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionPointedComparison
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionKanFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBoundaryKanFunctor
public import SerrePositivity.KST.Spectra.StrictEnrichedTransformationNerve

/-! # 元の S₁ 比較の Kan 後の厳密自然性と coherent nerve
概要：全入力族で自然な元の比較を、同じ Ex∞ と γ1 によって移す。
方針：厳密豊穣後合成を使い、成分が元の同じ比較の Ex∞ 像であることを回収する。
規約：逆射や比較の弱同値性を追加仮定しない。使われ方：BF 構造写像の源の span。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の S₁ 商比較を同じ Ex∞ で写した、実際の点つき Kan 比較。 -/
def presentedPerfectDGOneDirectionKanComparisonMap (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGOneDirectionKanEnrichedFunctor A r).obj C ⟶
      (presentedPerfectDGBoundaryKanEnrichedFunctor A r).obj C :=
  exInfinityPointedKanMap (presentedPerfectDGOneDirectionPointedComparisonMap A r C)

/-- 同じ元の比較は、Kan 後も全 native Hom 上の厳密豊穣自然変換。 -/
def presentedPerfectDGOneDirectionKanComparison (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      (presentedPerfectDGOneDirectionKanEnrichedFunctor A r)
      (presentedPerfectDGBoundaryKanEnrichedFunctor A r) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationPostcompose _ _ exInfinityPointedKanEnrichedFunctor
    (presentedPerfectDGOneDirectionPointedComparison A r)

/-- Kan 後の厳密自然変換の成分は、同じ元の比較の Ex∞ 像を回収する。 -/
lemma presentedPerfectDGOneDirectionKanComparison_app (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGOneDirectionKanComparison A r).app C =
      eHomEquiv SSet (presentedPerfectDGOneDirectionKanComparisonMap A r C) :=
  exInfinityPointedKanEnrichedFunctor_hom
    (presentedPerfectDGOneDirectionPointedComparisonMap A r C)

/-- 全入力の coherent nerve 上で同じ比較が与える、実際の単体区間族。 -/
def presentedPerfectDGOneDirectionKanComparisonHomotopy (r : ℕ) :
    SSet.Homotopy (presentedPerfectDGOneDirectionKanInfinityFunctor A r)
      (presentedPerfectDGBoundaryKanInfinityFunctor A r) :=
  Spectra.StrictEnrichedTransformation.homotopy _ _
    (presentedPerfectDGOneDirectionKanComparison A r)

end SerrePositivity.KST.SConstruction
