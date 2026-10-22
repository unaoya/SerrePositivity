module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFSOAPositiveAdjoint
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFSOAZeroStructure
public import SerrePositivity.KST.SConstruction.PointedComponentAdjointSquare

/-! # 元の旧 BF 列と新 BF 列の全構造射の点つき比較
概要：全段の前向き弱比較は、零段を含む全構造射と点つき成分で可換。
方針：全正随伴比較を uncurry し、旧単射置換の厳密射影と合成する。
規約：実スペクトル射への修正は別工程。使われ方：元の dgK との実比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet Spectra
open Spectra.PointedMapping SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 全正構造射は、元の前向き段比較で点つき成分が可換。 -/
lemma presentedPerfectDGBFRawSOAComparison_positive_structure (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    componentOf (PointedSimplicialSet.circle.{max (u + 1) v} ◁
        presentedPerfectDGBFRawSOAComparison A C (r + 1) ≫
          (presentedPerfectDGBFOmegaSpectrum A C).sigma (r + 1)) =
      componentOf (boundaryKanAssemblySigma r
          (stableCategoryModel (presentedPerfectDGStableCategory A C)) ≫
        presentedPerfectDGBFRawSOAComparison A C (r + 2)) := by
  exact pointedComponentAdjointSquare
    (presentedPerfectDGBFRawSOAComparison A C (r + 1))
    (presentedPerfectDGBFRawSOAComparison A C (r + 2))
    (boundaryKanAssemblyAdjoint r
      (stableCategoryModel (presentedPerfectDGStableCategory A C)))
    ((presentedPerfectDGBFOmegaSpectrum A C).sigma (r + 1))
    (presentedPerfectDGBFRawSOAComparison_positive_adjoint A r C)

/-- 元の K 候補列からの比較は零段を含む全構造射と点つき成分で可換。 -/
lemma presentedPerfectDGBFRawSOAComparison_structure
    (C : PerfDGInput.{u, v} A) (n : ℕ) :
    componentOf (PointedSimplicialSet.circle.{max (u + 1) v} ◁
        presentedPerfectDGBFRawSOAComparison A C n ≫
          (presentedPerfectDGBFOmegaSpectrum A C).sigma n) =
      componentOf
        ((kKanSequence (stableCategoryModel (presentedPerfectDGStableCategory A C))).sigma n ≫
          presentedPerfectDGBFRawSOAComparison A C (n + 1)) := by
  cases n with
  | zero => exact presentedPerfectDGBFRawSOAComparison_zero_structure A C
  | succ r => exact presentedPerfectDGBFRawSOAComparison_positive_structure A r C

/-- 同じ旧単射 BF K からの全段比較も、全構造射と点つき成分で可換。 -/
lemma presentedPerfectDGBFSOAComparison_structure
    (C : PerfDGInput.{u, v} A) (n : ℕ) :
    componentOf (PointedSimplicialSet.circle.{max (u + 1) v} ◁
        presentedPerfectDGBFSOAComparison A C n ≫
          (presentedPerfectDGBFOmegaSpectrum A C).sigma n) =
      componentOf
        ((kOmegaSpectrum (stableCategoryModel (presentedPerfectDGStableCategory A C))).sigma n ≫
          presentedPerfectDGBFSOAComparison A C (n + 1)) := by
  let p := monicKKanSequenceProjection
    (stableCategoryModel (presentedPerfectDGStableCategory A C))
  have h := componentOf_comp_left (presentedPerfectDGBFRawSOAComparison_structure A C n)
    (PointedSimplicialSet.circle.{max (u + 1) v} ◁ p.app n)
  change componentOf ((PointedSimplicialSet.circle.{max (u + 1) v} ◁
    (p.app n ≫ presentedPerfectDGBFRawSOAComparison A C n)) ≫ _) =
      componentOf (_ ≫ (p.app (n + 1) ≫ presentedPerfectDGBFRawSOAComparison A C (n + 1)))
  erw [whiskerLeft_comp]
  have hp := congrArg (fun f => componentOf
    (f ≫ presentedPerfectDGBFRawSOAComparison A C (n + 1))) (p.comm n)
  simp only [Category.assoc] at h hp ⊢
  exact h.trans hp

end SerrePositivity.KST.SConstruction
