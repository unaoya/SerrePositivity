module
public import SerrePositivity.KST.SConstruction.TracedTripleCorrectionPasting
public import SerrePositivity.KST.SConstruction.CorrectionInterchangePasting

/-! # 元の四補正面と両交換面の全六面を保つ三入力比較
概要：元の四面複体に元の両全交換三角形を貼り、左右の全補正辺路を同じ実複体へ接続する。
方針：元の全二辺と全対角辺の厳密な回収式を、二回の pushout に渡す。
規約：元の全六二単体を同時に保持し、Kan 充填で面を取り替えない。
使われ方：外側二入力の全段面・全二部分面・全正規化円柱を接続する。
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

/-- 元の全四補正面と同じ全二交換面を同時に保持する実複体の写像。 -/
def monicKTracedTripleInterchangePasting (n : ℕ) :
    correctionInterchangePasting.{u} ⟶
      (PointedObject.basedHom ((kOmegaSpectrum (F.obj w)).level n).space
        ((kKanSequence (F.obj z)).level n).space).right :=
  correctionInterchangePastingMap (monicKTracedTripleCorrectionPasting F f g h n)
    (SSet.yonedaEquiv.symm (monicKTracedTripleInterchangeDiamond F f g h n).second.simplex)
    (SSet.yonedaEquiv.symm (monicKTracedTripleInterchangeDiamond F f g h n).first.simplex)
    ((monicKTracedTripleCorrectionPasting_exchange_lower F f g h n).trans
      (SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm
        (monicKTracedTripleInterchangeDiamond F f g h n).second).symm)
    ((monicKTracedTripleCorrectionPasting_exchange_upper F f g h n).trans
      (SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm
        (monicKTracedTripleInterchangeDiamond F f g h n).second).symm)
    ((SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm
      (monicKTracedTripleInterchangeDiamond F f g h n).second).trans
        (SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm
          (monicKTracedTripleInterchangeDiamond F f g h n).first).symm)

/-- 元の全四面複体を厳密に回収する。 -/
lemma monicKTracedTripleInterchangePasting_original (n : ℕ) :
    correctionInterchangePastingOriginal ≫ monicKTracedTripleInterchangePasting F f g h n =
      monicKTracedTripleCorrectionPasting F f g h n :=
  correctionInterchangePastingMap_original _ _ _ _ _ _

/-- 元の全交換第一面を厳密に回収する。 -/
lemma monicKTracedTripleInterchangePasting_first (n : ℕ) :
    correctionInterchangePastingFirst ≫ monicKTracedTripleInterchangePasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedTripleInterchangeDiamond F f g h n).first.simplex :=
  correctionInterchangePastingMap_first _ _ _ _ _ _

/-- 元の全交換第二面も厳密に回収する。 -/
lemma monicKTracedTripleInterchangePasting_second (n : ℕ) :
    correctionInterchangePastingSecond ≫ monicKTracedTripleInterchangePasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedTripleInterchangeDiamond F f g h n).second.simplex :=
  correctionInterchangePastingMap_second _ _ _ _ _ _

/-- 元の前二射の全段面も、同じ実複体内の元の面そのもの。 -/
lemma monicKTracedTripleInterchangePasting_first_stage (n : ℕ) :
    triangleDiagonalPastingFirst ≫ doubleDiagonalTrianglePastingFirst 0 2 ≫
        correctionInterchangePastingOriginal ≫ monicKTracedTripleInterchangePasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairStageTriangle F f g h n).simplex := by
  rw [monicKTracedTripleInterchangePasting_original,
    monicKTracedTripleCorrectionPasting_first_stage]

/-- 元の前二射の全二部分面も、同じ実複体内の元の面そのもの。 -/
lemma monicKTracedTripleInterchangePasting_first_binary (n : ℕ) :
    triangleDiagonalPastingSecond ≫ doubleDiagonalTrianglePastingFirst 0 2 ≫
        correctionInterchangePastingOriginal ≫ monicKTracedTripleInterchangePasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairBinaryTriangle F f g h n).simplex := by
  rw [monicKTracedTripleInterchangePasting_original,
    monicKTracedTripleCorrectionPasting_first_binary]

/-- 元の後二射の全段面も、同じ実複体内の元の面そのもの。 -/
lemma monicKTracedTripleInterchangePasting_last_stage (n : ℕ) :
    triangleDiagonalPastingFirst ≫ doubleDiagonalTrianglePastingSecond 0 2 ≫
        correctionInterchangePastingOriginal ≫ monicKTracedTripleInterchangePasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedTripleLastPairStageTriangle F f g h n).simplex := by
  rw [monicKTracedTripleInterchangePasting_original,
    monicKTracedTripleCorrectionPasting_last_stage]

/-- 元の後二射の全二部分面も、同じ実複体内の元の面そのもの。 -/
lemma monicKTracedTripleInterchangePasting_last_binary (n : ℕ) :
    triangleDiagonalPastingSecond ≫ doubleDiagonalTrianglePastingSecond 0 2 ≫
        correctionInterchangePastingOriginal ≫ monicKTracedTripleInterchangePasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedTripleLastPairBinaryTriangle F f g h n).simplex := by
  rw [monicKTracedTripleInterchangePasting_original,
    monicKTracedTripleCorrectionPasting_last_binary]

/-- 左側の全補正辺は、元の左外側二部分面の同じ第二全辺。 -/
lemma monicKTracedTripleInterchangePasting_left_correction (n : ℕ) :
    stdSimplex.δ 2 ≫ correctionInterchangePastingFirst ≫
        monicKTracedTripleInterchangePasting F f g h n =
      stdSimplex.δ 0 ≫
        SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F (f ≫ g) h n).simplex := by
  rw [monicKTracedTripleInterchangePasting_first, SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]
  exact (monicKPrismCompositeBinaryPointTriangle_second_interchange F f g h n).symm

/-- 元の第二 BF whisker の全 raw 段辺を、同じ交換第一面の全上辺として回収する。 -/
lemma monicKTracedTripleInterchangePasting_second_whisker (n : ℕ) :
    stdSimplex.δ 0 ≫ correctionInterchangePastingFirst ≫
        monicKTracedTripleInterchangePasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedNativeSecondWhisker F f g h).edge ≫
        kRawMappingProjection (F.obj w) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n := by
  rw [monicKTracedTripleInterchangePasting_first, SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm]
  exact monicKTracedTripleInterchangeFirstUpper_whisker F f g h n

/-- 最初の全補正辺は、右外側二部分面の同じ第一全辺。 -/
lemma monicKTracedTripleInterchangePasting_first_path (n : ℕ) :
    stdSimplex.δ 2 ≫ triangleDiagonalPastingSecond ≫ doubleDiagonalTrianglePastingFirst 0 2 ≫
        correctionInterchangePastingOriginal ≫ monicKTracedTripleInterchangePasting F f g h n =
      stdSimplex.δ 2 ≫
        SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F f (g ≫ h) n).simplex := by
  rw [monicKTracedTripleInterchangePasting_original]
  exact monicKTracedTripleCorrectionPasting_first_path F f g h n

/-- 元の第一 BF whisker の全 raw 段辺も、同じ後二射段面の全上辺として回収する。 -/
lemma monicKTracedTripleInterchangePasting_first_whisker (n : ℕ) :
    stdSimplex.δ 0 ≫ triangleDiagonalPastingFirst ≫ doubleDiagonalTrianglePastingSecond 0 2 ≫
        correctionInterchangePastingOriginal ≫ monicKTracedTripleInterchangePasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedNativeFirstWhisker F f g h).edge ≫
        kRawMappingProjection (F.obj w) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n := by
  rw [monicKTracedTripleInterchangePasting_original]
  exact monicKTracedTripleCorrectionPasting_last_whisker F f g h n

end SerrePositivity.KST.SConstruction
