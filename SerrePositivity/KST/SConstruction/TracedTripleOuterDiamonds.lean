module
public import SerrePositivity.KST.SConstruction.TracedTripleOuterBinaryData
public import SerrePositivity.KST.SConstruction.TracedBFTripleDirectCorrectionComparison
public import SerrePositivity.KST.SConstruction.FixedCylinderComparisonAttachment

/-! # 元の左右段面を全正規化移送面と同じ二 diamond にする
概要：元の左右段面と同じ共有直接比較円柱を、六対角面消去の端点型へ合わせる。
方針：外側二部分面の全対角辺を基準に、元の全段面の端点表示を移す。
規約：両元の全段面・共有直接全円柱と、元の二部分面への移送を保持する。
使われ方：元の raw 各段の六つの実 diamond の外側二組。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の左外側全段面を、同じ全対角辺で表示する。 -/
def monicKTracedTripleLeftStageEdgeData (n : ℕ) :=
  triangleLongEdgeData (monicKTracedTripleLeftBinaryEdgeData F f g h n).direct
    (SSet.yonedaEquiv.symm
      (monicKTracedCompositionStageTriangleData F (f ≫ g) h n).triangle.simplex)
    ((SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm
      (monicKTracedCompositionStageTriangleData F (f ≫ g) h n).triangle).trans
      ((monicKPrismCompositeBinaryPointTriangle_direct F (f ≫ g) h n).symm.trans
        (monicKTracedTripleLeftBinaryEdgeData F f g h n).direct_map.symm))

/-- 同じ元の共有直接円柱を、左段面の指定第一辺から出る型へ合わせる。 -/
def monicKTracedTripleTypedDirectComparison (n : ℕ) :=
  fixedBoundarySourceCylinderData (monicKTracedTripleLeftStageEdgeData F f g h n).first
    (monicKTracedTripleDirectComparison F f g h n)
    ((monicKTracedTripleLeftStageEdgeData F f g h n).first_map.trans
      (SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm
        (monicKTracedCompositionStageTriangleData F (f ≫ g) h n).triangle))
    (fixedBoundaryHomotopy_source _ _ _
      (monicKTracedTripleDirectComparison_relative F f g h n))

/-- 元の右外側全段面を、同じ直接終辺・同じ全対角辺で表示する。 -/
def monicKTracedTripleRightStageEdgeData (n : ℕ) :=
  triangleLowerDirectData (monicKTracedTripleTypedDirectComparison F f g h n).target
    (monicKTracedTripleRightBinaryEdgeData F f g h n).direct
    (SSet.yonedaEquiv.symm
      (monicKTracedCompositionStageTriangleData F f (g ≫ h) n).triangle.simplex)
    ((SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm
      (monicKTracedCompositionStageTriangleData F f (g ≫ h) n).triangle).trans
      (monicKTracedTripleTypedDirectComparison F f g h n).target_map.symm)
    ((SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm
      (monicKTracedCompositionStageTriangleData F f (g ≫ h) n).triangle).trans
      ((monicKPrismCompositeBinaryPointTriangle_direct F f (g ≫ h) n).symm.trans
        (monicKTracedTripleRightBinaryEdgeData F f g h n).direct_map.symm))

/-- 左外側の元の段面と正規化移送面を持つ同じ実 diamond。 -/
def monicKTracedTripleLeftOuterDiamond (n : ℕ) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.mk (monicKTracedTripleLeftBinaryEdgeData F f g h n).direct
    (monicKTracedTripleLeftStageEdgeData F f g h n).triangle
    (monicKTracedTripleLeftBinaryTransport F f g h n)

/-- 右外側の元の段面と正規化移送面を持つ同じ実 diamond。 -/
def monicKTracedTripleRightOuterDiamond (n : ℕ) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CompositionDiamond.mk (monicKTracedTripleRightBinaryEdgeData F f g h n).direct
    (monicKTracedTripleRightStageEdgeData F f g h n).triangle
    (monicKTracedTripleRightBinaryTransport F f g h n)

/-- 共有直接比較は元の同じ全実円柱を厳密に保持する。 -/
lemma monicKTracedTripleTypedDirectComparison_h (n : ℕ) :
    (monicKTracedTripleTypedDirectComparison F f g h n).cylinder.homotopy.h =
      (monicKTracedTripleDirectComparison F f g h n).h :=
  (monicKTracedTripleTypedDirectComparison F f g h n).cylinder_h

/-- 左外側 diamond の第一全面は元の同じ全段面。 -/
lemma monicKTracedTripleLeftOuterDiamond_stage (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleLeftOuterDiamond F f g h n).first.simplex =
      SSet.yonedaEquiv.symm
        (monicKTracedCompositionStageTriangleData F (f ≫ g) h n).triangle.simplex :=
  (monicKTracedTripleLeftStageEdgeData F f g h n).realization_eq

/-- 右外側 diamond の第一全面も元の同じ全段面。 -/
lemma monicKTracedTripleRightOuterDiamond_stage (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleRightOuterDiamond F f g h n).first.simplex =
      SSet.yonedaEquiv.symm
        (monicKTracedCompositionStageTriangleData F f (g ≫ h) n).triangle.simplex :=
  (monicKTracedTripleRightStageEdgeData F f g h n).realization_eq

end SerrePositivity.KST.SConstruction
