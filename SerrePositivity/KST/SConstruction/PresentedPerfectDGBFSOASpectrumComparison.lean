module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFSOAStructure
public import SerrePositivity.KST.Spectra.SequenceHomotopyRectification
public import SerrePositivity.KST.Spectra.SpectrumHomotopyEquivalences

/-! # 元の SOA K から新 BF K への実スペクトル比較
概要：全構造射の点つき成分比較を、同じ両対象間の厳密 BF 射へ修正する。
方針：既存の単射構造射に沿う点ごとの修正を適用し、各段の元の弱比較を保持する。
規約：入力全体の豊穣作用は選び直さない。使われ方：元の dgK との実弱同値比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open Spectra.PointedMapping SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ旧単射 K 列から新 BF 列への、構造射と厳密に可換な実比較。 -/
def presentedPerfectDGBFSOASequenceComparison (C : PerfDGInput.{u, v} A) :
    KanSequence.Hom
      (kOmegaSpectrum (stableCategoryModel (presentedPerfectDGStableCategory A C))).toKanSequence
      (presentedPerfectDGBFOmegaSpectrum A C).toKanSequence :=
  KanSequence.rectify
    (kOmegaSpectrum (stableCategoryModel (presentedPerfectDGStableCategory A C))).sigma_mono
    (presentedPerfectDGBFSOAComparison A C) (presentedPerfectDGBFSOAComparison_structure A C)

/-- 同じ旧 SOA BF K から新 BF K への実際の厳密スペクトル射。 -/
def presentedPerfectDGBFSOASpectrumComparison (C : PerfDGInput.{u, v} A) :
    kOmegaSpectrum (stableCategoryModel (presentedPerfectDGStableCategory A C)) ⟶
      presentedPerfectDGBFOmegaSpectrum A C where
  app := (presentedPerfectDGBFSOASequenceComparison A C).app
  comm := (presentedPerfectDGBFSOASequenceComparison A C).comm

/-- 同じ実スペクトル比較は、全段で元の前向き弱比較の点つき成分を保つ。 -/
lemma presentedPerfectDGBFSOASpectrumComparison_component
    (C : PerfDGInput.{u, v} A) (n : ℕ) :
    componentOf ((presentedPerfectDGBFSOASpectrumComparison A C).app n) =
      componentOf (presentedPerfectDGBFSOAComparison A C n) :=
  KanSequence.rectify_component _ _ _ n

/-- 同じ実スペクトル比較は、零段を含む全段で全基点 π 同型。 -/
lemma presentedPerfectDGBFSOASpectrumComparison_levelwise
    (C : PerfDGInput.{u, v} A) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((presentedPerfectDGBFSOASpectrumComparison A C).app n).right :=
  KanSequence.rectify_levelwise _ _ _ (presentedPerfectDGBFSOAComparison_piIsomorphism A C) n

/-- 同じ実 BF 比較射は全整数次数で π 同型。 -/
lemma presentedPerfectDGBFSOASpectrumComparison_piIsomorphism
    (C : PerfDGInput.{u, v} A) :
    OmegaSpectrum.PiIsomorphism (presentedPerfectDGBFSOASpectrumComparison A C) :=
  OmegaSpectrum.piIsomorphism_of_levelwise _
    (presentedPerfectDGBFSOASpectrumComparison_levelwise A C)

/-- 同じ実スペクトル比較の零段は、元の二 Kan 模型の loop 比較を保つ。 -/
lemma presentedPerfectDGBFSOASpectrumComparison_zero (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBFSOASpectrumComparison A C).app 0 =
      presentedPerfectDGBFSOAComparison A C 0 := rfl

end SerrePositivity.KST.SConstruction
