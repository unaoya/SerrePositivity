module
public import SerrePositivity.KST.SConstruction.TracedTripleOuterDiamonds
public import SerrePositivity.KST.SConstruction.TracedTripleRawDiagramPasting

/-! # 元の BF 二面を他の四 diamond と同じ端点型で回収する
概要：元の全 BF 二単体の raw 段評価を、既存の右段辺と両 whisker へ接続する。
方針：全三辺の厳密な式から端点表示だけを揃え、元の共有全対角辺を保つ。
規約：BF 全二面を選び直さず、元の同じ全 raw 評価として回収する。
使われ方：元の各段の六対角面を実消去へ渡す最後の diamond。
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

/-- 元の第一 BF 全面を、元の右段辺と第一 whisker で表示する。 -/
def monicKTracedTripleBFFirstEdgeData (n : ℕ) :=
  trianglePairEdgeData (monicKTracedTripleRightStageEdgeData F f g h n).second
    (monicKTracedTripleLastStageEdgeData F f g h n).second
    (monicKTracedTripleRawFirstTriangle F f g h n)
    (by
      unfold monicKTracedTripleRawFirstTriangle
      simp only [← Category.assoc, SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]
      simp only [Category.assoc]
      exact (monicKTracedCompositionRawStageEdge_map F f (g ≫ h) n).symm.trans
        ((SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm
          (monicKTracedCompositionStageTriangleData F f (g ≫ h) n).triangle).symm.trans
            (monicKTracedTripleRightStageEdgeData F f g h n).second_map.symm))
    (by
      unfold monicKTracedTripleRawFirstTriangle
      simp only [← Category.assoc, SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm]
      simp only [Category.assoc]
      exact (monicKTracedTripleLastPairStageTriangle_upper F f g h n).symm.trans
        (monicKTracedTripleLastStageEdgeData F f g h n).second_map.symm)

/-- 元の第二 BF 全面を、同じ全対角辺と第二 whisker で表示する。 -/
def monicKTracedTripleBFSecondEdgeData (n : ℕ) :=
  triangleUpperDirectData (monicKTracedTripleInterchangeFirstUpper F f g h n)
    (monicKTracedTripleBFFirstEdgeData F f g h n).direct
    (monicKTracedTripleRawSecondTriangle F f g h n)
    (by
      unfold monicKTracedTripleRawSecondTriangle
      simp only [← Category.assoc, SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm]
      simp only [Category.assoc]
      exact (monicKTracedTripleInterchangeFirstUpper_whisker F f g h n).symm)
    ((monicKTracedTripleRawTriangles_diagonal F f g h n).symm.trans
      (monicKTracedTripleBFFirstEdgeData F f g h n).direct_map.symm)

/-- 元の同じ BF 全二面を持ち、他の五組と端点型の揃った実 diamond。 -/
def monicKTracedTripleBFDiamond (n : ℕ) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.mk (monicKTracedTripleBFFirstEdgeData F f g h n).direct
    (monicKTracedTripleBFFirstEdgeData F f g h n).triangle
    (monicKTracedTripleBFSecondEdgeData F f g h n).triangle

/-- 第一全面は元の同じ native BF 全面の全 raw 段評価。 -/
lemma monicKTracedTripleBFDiamond_first (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleBFDiamond F f g h n).first.simplex =
      monicKTracedTripleRawFirstTriangle F f g h n :=
  (monicKTracedTripleBFFirstEdgeData F f g h n).realization_eq

/-- 第二全面も元の同じ native BF 全面の全 raw 段評価。 -/
lemma monicKTracedTripleBFDiamond_second (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleBFDiamond F f g h n).second.simplex =
      monicKTracedTripleRawSecondTriangle F f g h n :=
  (monicKTracedTripleBFSecondEdgeData F f g h n).realization_eq

end SerrePositivity.KST.SConstruction
