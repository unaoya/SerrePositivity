module
public import SerrePositivity.KST.SConstruction.TracedTripleCorrectionPathFaces
public import SerrePositivity.KST.SConstruction.TriangleTwoEdgeData
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.TriangleDiamondComposition

/-! # 元の前後二射の四面を交換面と同じ端点の二 diamond へ束ねる
概要：前後二射の段面と二部分面を、同じ交換二辺に沿う実 diamond として回収する。
方針：全共有辺の既存の厳密な式で、元の二単体の端点表示だけを移す。
規約：元の四つの全二単体と共通中間辺を保持し、新しい三角形を充填しない。
使われ方：元の raw 各段の六対角面を実四面体の消去へ渡す。
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

/-- 元の前二射段面を交換第二下面と同じ端点で回収する。 -/
def monicKTracedTripleFirstStageEdgeData (n : ℕ) :=
  triangleUpperEdgeData (monicKTracedTripleInterchangeSecondLower F f g h n)
    (SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairStageTriangle F f g h n).simplex)
    (monicKTracedTripleFirstPairStageTriangle_upper F f g h n)

/-- 元の前二射二部分面を、その同じ全対角辺に合わせる。 -/
def monicKTracedTripleFirstBinaryEdgeData (n : ℕ) :=
  triangleLongEdgeData (monicKTracedTripleFirstStageEdgeData F f g h n).direct
    (SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairBinaryTriangle F f g h n).simplex)
    ((monicKTracedTripleFirstPairBinaryTriangle_direct F f g h n).trans
      (monicKTracedTripleFirstStageEdgeData F f g h n).direct_map.symm)

/-- 前二射の元の同じ全段面と全二部分面を持つ、型の揃った実 diamond。 -/
def monicKTracedTripleFirstPairDiamond (n : ℕ) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.mk (monicKTracedTripleFirstStageEdgeData F f g h n).direct
    (monicKTracedTripleFirstStageEdgeData F f g h n).triangle
    (monicKTracedTripleFirstBinaryEdgeData F f g h n).triangle

/-- 元の後二射二部分面を同じ中間全辺と交換第二上辺で回収する。 -/
def monicKTracedTripleLastBinaryEdgeData (n : ℕ) :=
  trianglePairEdgeData (monicKTracedTripleFirstBinaryEdgeData F f g h n).second
    (monicKTracedTripleInterchangeSecondUpper F f g h n)
    (SSet.yonedaEquiv.symm (monicKTracedTripleLastPairBinaryTriangle F f g h n).simplex)
    ((monicKTracedTripleCorrectionPath_middle F f g h n).symm.trans
      (monicKTracedTripleFirstBinaryEdgeData F f g h n).second_map.symm)
    (monicKTracedTripleCorrectionPath_last F f g h n)

/-- 元の後二射段面を、その同じ全対角辺に合わせる。 -/
def monicKTracedTripleLastStageEdgeData (n : ℕ) :=
  triangleLongEdgeData (monicKTracedTripleLastBinaryEdgeData F f g h n).direct
    (SSet.yonedaEquiv.symm (monicKTracedTripleLastPairStageTriangle F f g h n).simplex)
    ((monicKTracedTripleLastPairBinaryTriangle_direct F f g h n).symm.trans
      (monicKTracedTripleLastBinaryEdgeData F f g h n).direct_map.symm)

/-- 後二射の元の同じ全段面と全二部分面を持つ、型の揃った実 diamond。 -/
def monicKTracedTripleLastPairDiamond (n : ℕ) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.mk (monicKTracedTripleLastBinaryEdgeData F f g h n).direct
    (monicKTracedTripleLastStageEdgeData F f g h n).triangle
    (monicKTracedTripleLastBinaryEdgeData F f g h n).triangle

/-- 前二射の第一全三角形は元の同じ全段面。 -/
lemma monicKTracedTripleFirstPairDiamond_stage (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairDiamond F f g h n).first.simplex =
      SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairStageTriangle F f g h n).simplex :=
  (monicKTracedTripleFirstStageEdgeData F f g h n).realization_eq

/-- 前二射の第二全三角形は元の同じ全二部分面。 -/
lemma monicKTracedTripleFirstPairDiamond_binary (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairDiamond F f g h n).second.simplex =
      SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairBinaryTriangle F f g h n).simplex :=
  (monicKTracedTripleFirstBinaryEdgeData F f g h n).realization_eq

/-- 後二射の第一全三角形は元の同じ全段面。 -/
lemma monicKTracedTripleLastPairDiamond_stage (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleLastPairDiamond F f g h n).first.simplex =
      SSet.yonedaEquiv.symm (monicKTracedTripleLastPairStageTriangle F f g h n).simplex :=
  (monicKTracedTripleLastStageEdgeData F f g h n).realization_eq

/-- 後二射の第二全三角形は元の同じ全二部分面。 -/
lemma monicKTracedTripleLastPairDiamond_binary (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleLastPairDiamond F f g h n).second.simplex =
      SSet.yonedaEquiv.symm (monicKTracedTripleLastPairBinaryTriangle F f g h n).simplex :=
  (monicKTracedTripleLastBinaryEdgeData F f g h n).realization_eq

end SerrePositivity.KST.SConstruction
