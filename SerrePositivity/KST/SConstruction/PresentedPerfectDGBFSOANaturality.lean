module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFSOARawNaturality
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFSOASpectrumComparison
public import SerrePositivity.KST.SConstruction.PointedComponentSquareComposition
public import SerrePositivity.KST.SConstruction.KStageHomotopyFunctor

/-! # 同じ実 SOA・新 BF スペクトル比較の全段入力自然性
概要：保存済みの同じ実比較射は、全入力射と全段の点つき成分で自然。
方針：旧置換射影の成分自然性と元の候補列比較を合成し、修正が保つ成分を使う。
規約：BF 写像空間全体の成分とは主張しない。使われ方：整数 π 比較の自然性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open Spectra.PointedMapping SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 旧単射 BF K からの同じ全段比較は、元の入力射と全段で成分が自然。 -/
lemma presentedPerfectDGBFSOAComparison_naturality
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) (n : ℕ) :
    componentOf ((kSpectrumMap (presentedPerfectDGBFInputStableMap A f)).app n ≫
        presentedPerfectDGBFSOAComparison A Y n) =
      componentOf (presentedPerfectDGBFSOAComparison A X n ≫
        (presentedPerfectDGBFMap A f).app n) :=
  pointedComponentSquareComposition
    ((kSpectrumMap (presentedPerfectDGBFInputStableMap A f)).app n)
    (kKanSequenceLevelMap (presentedPerfectDGBFInputStableMap A f) n)
    ((monicKKanSequenceProjection
      (stableCategoryModel (presentedPerfectDGStableCategory A X))).app n)
    ((monicKKanSequenceProjection
      (stableCategoryModel (presentedPerfectDGStableCategory A Y))).app n)
    (presentedPerfectDGBFRawSOAComparison A X n)
    (presentedPerfectDGBFRawSOAComparison A Y n) ((presentedPerfectDGBFMap A f).app n)
    (monicKKanSequenceMap_projection_component (presentedPerfectDGBFInputStableMap A f) n)
    (presentedPerfectDGBFRawSOAComparison_naturality A f n)

/-- 同じ実 SOA→新 BF スペクトル比較は、元の入力射と全段で成分が自然。 -/
lemma presentedPerfectDGBFSOASpectrumComparison_naturality_component
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) (n : ℕ) :
    componentOf ((kSpectrumMap (presentedPerfectDGBFInputStableMap A f)).app n ≫
        (presentedPerfectDGBFSOASpectrumComparison A Y).app n) =
      componentOf ((presentedPerfectDGBFSOASpectrumComparison A X).app n ≫
        (presentedPerfectDGBFMap A f).app n) := by
  have hy := componentOf_comp_left
    (presentedPerfectDGBFSOASpectrumComparison_component A Y n)
    ((kSpectrumMap (presentedPerfectDGBFInputStableMap A f)).app n)
  have hx := componentOf_comp_right
    (presentedPerfectDGBFSOASpectrumComparison_component A X n)
    ((presentedPerfectDGBFMap A f).app n)
  exact hy.trans ((presentedPerfectDGBFSOAComparison_naturality A f n).trans hx.symm)

/-- 同じ実比較射は、全段・全自然数次数の基点付きホモトピー集合で入力に自然。 -/
lemma presentedPerfectDGBFSOASpectrumComparison_pointedHomotopy_naturality
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) (n m : ℕ) :
    pointedHomotopyMap m
        ((kSpectrumMap (presentedPerfectDGBFInputStableMap A f)).app n ≫
          (presentedPerfectDGBFSOASpectrumComparison A Y).app n) =
      pointedHomotopyMap m
        ((presentedPerfectDGBFSOASpectrumComparison A X).app n ≫
          (presentedPerfectDGBFMap A f).app n) :=
  pointedHomotopyMap_eq_of_component
    (presentedPerfectDGBFSOASpectrumComparison_naturality_component A f n) m

end SerrePositivity.KST.SConstruction
