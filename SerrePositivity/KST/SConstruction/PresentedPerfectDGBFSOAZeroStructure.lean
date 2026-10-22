module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFSOAComparison
public import SerrePositivity.KST.SConstruction.PointedEnrichedCylinderComponents

/-! # 元の SOA K 列と新 BF 列の零構造射の比較
概要：前向き零段・第一段比較は、同じ元の評価と実円柱を点つき成分で結ぶ。
方針：元の評価の自然性と、同じ最初の円柱源射の成分を使う。
規約：列全体の厳密比較は別工程。使われ方：元の dgK との比較の基底。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet Spectra
open Spectra.PointedMapping SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ元の K 候補列と新 BF 列の零構造射は、前向き比較で点つき成分が可換。 -/
lemma presentedPerfectDGBFRawSOAComparison_zero_structure (C : PerfDGInput.{u, v} A) :
    componentOf
        (PointedSimplicialSet.circle.{max (u + 1) v} ◁
            presentedPerfectDGBFRawSOAComparison A C 0 ≫
          (presentedPerfectDGBFOmegaSpectrum A C).sigma 0) =
      componentOf
        ((kKanSequence (stableCategoryModel (presentedPerfectDGStableCategory A C))).sigma 0 ≫
          presentedPerfectDGBFRawSOAComparison A C 1) := by
  let b := presentedPerfectDGBFBoundarySOAComparison A 0 C
  let j : ((presentedPerfectDGBFBaseFunctor A).obj C).obj ⟶
      ((presentedPerfectDGBFFirstFunctor A).obj C).obj :=
    presentedPerfectDGBFFirstComparison A C
  have h := componentOf_comp_left
    (pointedEnrichedMonicReplacementSource_component
      (presentedPerfectDGBFZeroSuspensionFunctor A) (presentedPerfectDGBFBaseFunctor A)
      (presentedPerfectDGBFZeroEvaluation A) (presentedPerfectDGBFZeroEvaluation_whisker A) C)
    (PointedSimplicialSet.circle.{max (u + 1) v} ◁
      (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{max (u + 1) v}).map b)
  refine h.trans ?_
  apply congrArg componentOf
  change (PointedSimplicialSet.circle.{max (u + 1) v} ◁
    (ihom PointedSimplicialSet.circle.{max (u + 1) v}).map b) ≫
      ((ihom.ev PointedSimplicialSet.circle.{max (u + 1) v}).app _ ≫ j) = _
  erw [← Category.assoc, ihom.ev_naturality, Category.assoc]
  change (ihom.ev PointedSimplicialSet.circle.{max (u + 1) v}).app _ ≫ b ≫ j =
    uncurry (𝟙 _) ≫ (b ≫ j)
  rw [uncurry_id_eq_ev]
  rfl

end SerrePositivity.KST.SConstruction
