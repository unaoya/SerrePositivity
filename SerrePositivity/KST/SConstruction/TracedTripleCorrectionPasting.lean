module
public import SerrePositivity.KST.SConstruction.TracedTriplePairCorrectionPasting
public import SerrePositivity.KST.SConstruction.DoubleDiagonalTrianglePasting

/-! # 元の四つの補正比較面の同じ実貼り合わせ複体
概要：前二射・後二射の段面と二部分面を、共有する同じ全中間補正辺で貼り合わせる。
方針：元の四つの全二単体の像を保持する二段の pushout と、全辺の厳密な式を使う。
規約：各全三角形と交換面に接する両全辺を厳密に回収し、面を選び直さない。
使われ方：元の実交換面・外側面・全正規化円柱を同じ補正辺路へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の四つの全補正比較面を、同じ中間全辺で貼り合わせた実写像。 -/
def monicKTracedTripleCorrectionPasting (n : ℕ) :=
  doubleDiagonalTrianglePastingMap 0 2
    (monicKTracedTripleFirstPairCorrectionPasting F f g h n)
    (monicKTracedTripleLastPairCorrectionPasting F f g h n)
    (by
      simp only [Category.assoc, monicKTracedTripleFirstPairCorrectionPasting_binary,
        monicKTracedTripleLastPairCorrectionPasting_binary]
      exact monicKTracedTripleCorrectionPath_middle F f g h n)

/-- 元の前二射の全段面を、同じ実複体から厳密に回収する。 -/
lemma monicKTracedTripleCorrectionPasting_first_stage (n : ℕ) :
    triangleDiagonalPastingFirst ≫ doubleDiagonalTrianglePastingFirst 0 2 ≫
        monicKTracedTripleCorrectionPasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairStageTriangle F f g h n).simplex := by
  rw [monicKTracedTripleCorrectionPasting, doubleDiagonalTrianglePastingMap_first,
    monicKTracedTripleFirstPairCorrectionPasting_stage]

/-- 元の前二射の全二部分面も、同じ実複体から厳密に回収する。 -/
lemma monicKTracedTripleCorrectionPasting_first_binary (n : ℕ) :
    triangleDiagonalPastingSecond ≫ doubleDiagonalTrianglePastingFirst 0 2 ≫
        monicKTracedTripleCorrectionPasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairBinaryTriangle F f g h n).simplex := by
  rw [monicKTracedTripleCorrectionPasting, doubleDiagonalTrianglePastingMap_first,
    monicKTracedTripleFirstPairCorrectionPasting_binary]

/-- 元の後二射の全段面も、同じ実複体から厳密に回収する。 -/
lemma monicKTracedTripleCorrectionPasting_last_stage (n : ℕ) :
    triangleDiagonalPastingFirst ≫ doubleDiagonalTrianglePastingSecond 0 2 ≫
        monicKTracedTripleCorrectionPasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedTripleLastPairStageTriangle F f g h n).simplex := by
  rw [monicKTracedTripleCorrectionPasting, doubleDiagonalTrianglePastingMap_second,
    monicKTracedTripleLastPairCorrectionPasting_stage]

/-- 元の後二射の全二部分面も、同じ実複体から厳密に回収する。 -/
lemma monicKTracedTripleCorrectionPasting_last_binary (n : ℕ) :
    triangleDiagonalPastingSecond ≫ doubleDiagonalTrianglePastingSecond 0 2 ≫
        monicKTracedTripleCorrectionPasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedTripleLastPairBinaryTriangle F f g h n).simplex := by
  rw [monicKTracedTripleCorrectionPasting, doubleDiagonalTrianglePastingMap_second,
    monicKTracedTripleLastPairCorrectionPasting_binary]

/-- 元の最初の全補正辺は、右外側二部分面の同じ全下面。 -/
lemma monicKTracedTripleCorrectionPasting_first_path (n : ℕ) :
    stdSimplex.δ 2 ≫ triangleDiagonalPastingSecond ≫
        doubleDiagonalTrianglePastingFirst 0 2 ≫ monicKTracedTripleCorrectionPasting F f g h n =
      stdSimplex.δ 2 ≫
        SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F f (g ≫ h) n).simplex := by
  rw [monicKTracedTripleCorrectionPasting_first_binary]
  exact monicKTracedTripleCorrectionPath_first F f g h n

/-- 交換面の元の第二下辺全体を、同じ実複体の元の段面から厳密に回収する。 -/
lemma monicKTracedTripleCorrectionPasting_exchange_lower (n : ℕ) :
    stdSimplex.δ 0 ≫ triangleDiagonalPastingFirst ≫
        doubleDiagonalTrianglePastingFirst 0 2 ≫ monicKTracedTripleCorrectionPasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedTripleInterchangeSecondLower F f g h n).edge := by
  rw [monicKTracedTripleCorrectionPasting_first_stage]
  exact monicKTracedTripleFirstPairStageTriangle_upper F f g h n

/-- 交換面の元の第二上辺全体も、同じ実複体の元の二部分面から厳密に回収する。 -/
lemma monicKTracedTripleCorrectionPasting_exchange_upper (n : ℕ) :
    stdSimplex.δ 0 ≫ triangleDiagonalPastingSecond ≫
        doubleDiagonalTrianglePastingSecond 0 2 ≫ monicKTracedTripleCorrectionPasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedTripleInterchangeSecondUpper F f g h n).edge := by
  rw [monicKTracedTripleCorrectionPasting_last_binary]
  exact monicKTracedTripleCorrectionPath_last F f g h n

/-- 元の第一 BF whisker の全 raw 段辺も、同じ実複体の後二射段面から厳密に回収する。 -/
lemma monicKTracedTripleCorrectionPasting_last_whisker (n : ℕ) :
    stdSimplex.δ 0 ≫ triangleDiagonalPastingFirst ≫
        doubleDiagonalTrianglePastingSecond 0 2 ≫ monicKTracedTripleCorrectionPasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedNativeFirstWhisker F f g h).edge ≫
        kRawMappingProjection (F.obj w) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n := by
  rw [monicKTracedTripleCorrectionPasting_last_stage]
  exact monicKTracedTripleLastPairStageTriangle_upper F f g h n

end SerrePositivity.KST.SConstruction
