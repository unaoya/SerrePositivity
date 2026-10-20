module
public import SerrePositivity.KST.SConstruction.TracedTripleCorrectionPathFaces
public import SerrePositivity.KST.SConstruction.TriangleDiagonalPasting

/-! # 元の前後二射の段面と二部分面の実貼り合わせ
概要：元の前二射・後二射について、段三角形と二部分三角形を同じ全対角補正辺で貼る。
方針：証明済みの全対角辺の厳密な一致を、同じ標準二三角形の pushout へ渡す。
規約：元の四つの全二単体を同じ実複体の像として保持し、充填し直さない。
使われ方：左右三本補正辺路と元の交換面を同じ比較複体へ接続する。
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

/-- 元の前二射の段三角形と二部分三角形の、同じ対角での実貼り合わせ写像。 -/
def monicKTracedTripleFirstPairCorrectionPasting (n : ℕ) :=
  triangleDiagonalPastingMap
    (SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairStageTriangle F f g h n).simplex)
    (SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairBinaryTriangle F f g h n).simplex)
    (monicKTracedTripleFirstPairBinaryTriangle_direct F f g h n).symm

/-- 元の後二射の段三角形と二部分三角形の、同じ対角での実貼り合わせ写像。 -/
def monicKTracedTripleLastPairCorrectionPasting (n : ℕ) :=
  triangleDiagonalPastingMap
    (SSet.yonedaEquiv.symm (monicKTracedTripleLastPairStageTriangle F f g h n).simplex)
    (SSet.yonedaEquiv.symm (monicKTracedTripleLastPairBinaryTriangle F f g h n).simplex)
    (monicKTracedTripleLastPairBinaryTriangle_direct F f g h n).symm

/-- 元の前二射の全段三角形は、同じ実複体の第一面そのもの。 -/
lemma monicKTracedTripleFirstPairCorrectionPasting_stage (n : ℕ) :
    triangleDiagonalPastingFirst ≫ monicKTracedTripleFirstPairCorrectionPasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairStageTriangle F f g h n).simplex :=
  triangleDiagonalPastingMap_first _ _ _

/-- 元の前二射の全二部分三角形も、同じ実複体の第二面そのもの。 -/
lemma monicKTracedTripleFirstPairCorrectionPasting_binary (n : ℕ) :
    triangleDiagonalPastingSecond ≫ monicKTracedTripleFirstPairCorrectionPasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairBinaryTriangle F f g h n).simplex :=
  triangleDiagonalPastingMap_second _ _ _

/-- 元の後二射の全段三角形も、同じ実複体の第一面そのもの。 -/
lemma monicKTracedTripleLastPairCorrectionPasting_stage (n : ℕ) :
    triangleDiagonalPastingFirst ≫ monicKTracedTripleLastPairCorrectionPasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedTripleLastPairStageTriangle F f g h n).simplex :=
  triangleDiagonalPastingMap_first _ _ _

/-- 元の後二射の全二部分三角形も、同じ実複体の第二面そのもの。 -/
lemma monicKTracedTripleLastPairCorrectionPasting_binary (n : ℕ) :
    triangleDiagonalPastingSecond ≫ monicKTracedTripleLastPairCorrectionPasting F f g h n =
      SSet.yonedaEquiv.symm (monicKTracedTripleLastPairBinaryTriangle F f g h n).simplex :=
  triangleDiagonalPastingMap_second _ _ _

end SerrePositivity.KST.SConstruction
