module
public import SerrePositivity.KST.SConstruction.TracedBFWhiskerZeroEvaluation
public import SerrePositivity.KST.SConstruction.ConstantDiamondEdgeComparison
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CompositionDiamondImages

/-! # 生成第四辺と元の指定左 BF 辺の零段実比較
概要：元の BF 三辺の零段定数性と同じ二三角形から、第四辺の零段比較を実構成する。
方針：全二三角形を零段評価し、定数三辺の端点固定比較を適用する。
規約：元の全零段二単体を同じ高次比較に保持する。全段の raw 比較はまだ主張しない。
使われ方：第四辺 raw 比較の相対逐次構成の実零段。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance tracedTripleZeroSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の BF 始終写像空間の同じ零段評価。 -/
def monicKTracedTripleZeroEvaluation :=
  OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj w)) (kOmegaSpectrum (F.obj z)) 0

/-- 元の同じ BF 二三角形と共通対角辺の全零段像。 -/
def monicKTracedTripleZeroDiamond :=
  (monicKTracedNativeTripleCompositionDiamond F f g h).map
    (monicKTracedTripleZeroEvaluation (w := w) (z := z) F)

/-- 第一の元の下辺は全零段で定数。 -/
lemma monicKTracedTripleZeroLower_constant :
    ∃ v, SSet.yonedaEquiv.symm ((monicKTracedSpectrumCompositionEdge F f (g ≫ h)).map
      (monicKTracedTripleZeroEvaluation (w := w) (z := z) F)).edge = SSet.const v :=
  constantEdge_map _ _ ⟨_, monicKTracedSpectrumCompositionEdge_zero F f (g ≫ h)⟩

/-- 第一の元の上辺は全零段で定数。 -/
lemma monicKTracedTripleZeroFirstWhisker_constant :
    ∃ v, SSet.yonedaEquiv.symm ((monicKTracedNativeFirstWhisker F f g h).map
      (monicKTracedTripleZeroEvaluation (w := w) (z := z) F)).edge = SSet.const v :=
  constantEdge_map _ _ (monicKTracedNativeFirstWhisker_zero_constant F f g h)

/-- 第二の元の上辺も全零段で定数。 -/
lemma monicKTracedTripleZeroSecondWhisker_constant :
    ∃ v, SSet.yonedaEquiv.symm ((monicKTracedNativeSecondWhisker F f g h).map
      (monicKTracedTripleZeroEvaluation (w := w) (z := z) F)).edge = SSet.const v :=
  constantEdge_map _ _ (monicKTracedNativeSecondWhisker_zero_constant F f g h)

/-- 独立に指定した元の左 BF 比較辺も全零段で定数。 -/
lemma monicKTracedTripleZeroPrescribed_constant :
    ∃ v, SSet.yonedaEquiv.symm ((monicKTracedNativeTriplePrescribedEdge F f g h).map
      (monicKTracedTripleZeroEvaluation (w := w) (z := z) F)).edge = SSet.const v :=
  constantEdge_map _ _ (monicKTracedNativeTriplePrescribedEdge_zero_constant F f g h)

/-- 元の指定左辺から生成第四辺への、元の全二三角形を保持する全端点固定零段比較。 -/
def monicKTracedTripleZeroComparison :=
  constantDiamondEdgeComparison (monicKTracedTripleZeroDiamond F f g h)
    (monicKTracedTripleZeroLower_constant F f g h)
    (monicKTracedTripleZeroFirstWhisker_constant F f g h)
    (monicKTracedTripleZeroSecondWhisker_constant F f g h)
    (monicKTracedTripleZeroPrescribed_constant F f g h)

/-- 元の二三角形の全零段像を面に保持する同じ実高次比較。 -/
def monicKTracedTripleZeroComparisonRealization :=
  constantDiamondEdgeComparisonRealization (monicKTracedTripleZeroDiamond F f g h)
    (monicKTracedTripleZeroLower_constant F f g h)
    (monicKTracedTripleZeroFirstWhisker_constant F f g h)
    (monicKTracedTripleZeroSecondWhisker_constant F f g h)
    (monicKTracedTripleZeroPrescribed_constant F f g h)

/-- 同じ高次比較の指定面は、構成した全端点固定零段円柱そのもの。 -/
lemma monicKTracedTripleZeroComparisonRealization_comparison :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 2) ≫
        monicKTracedTripleZeroComparisonRealization F f g h =
      (monicKTracedTripleZeroComparison F f g h).homotopy.h :=
  constantDiamondEdgeComparisonRealization_comparison _ _ _ _ _

/-- 第一の元の全二単体の零段像を、そのまま同じ高次比較の指定面に保持する。 -/
lemma monicKTracedTripleZeroComparisonRealization_first_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 1) ≫
        monicKTracedTripleZeroComparisonRealization F f g h =
      SSet.yonedaEquiv.symm ((monicKTracedTripleZeroEvaluation (w := w) (z := z) F).app
        (Opposite.op ⦋2⦌) (monicKTracedNativeTripleCompositionDiamond F f g h).first.simplex) :=
  constantDiamondEdgeComparisonRealization_first_triangle _ _ _ _ _

/-- 第二の元の全二単体の零段像も、同じ高次比較の指定面に保持する。 -/
lemma monicKTracedTripleZeroComparisonRealization_second_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 0) ≫
        monicKTracedTripleZeroComparisonRealization F f g h =
      SSet.yonedaEquiv.symm ((monicKTracedTripleZeroEvaluation (w := w) (z := z) F).app
        (Opposite.op ⦋2⦌) (monicKTracedNativeTripleCompositionDiamond F f g h).second.simplex) :=
  constantDiamondEdgeComparisonRealization_second_triangle _ _ _ _ _

/-- 元の全零段高次比較は、全パラメータで元の全区間境界を厳密に固定する。 -/
lemma monicKTracedTripleZeroComparisonRealization_relative :
    ((SSet.boundary 1).ι ▷ (Δ[2] : SSet.{u})) ≫
        monicKTracedTripleZeroComparisonRealization F f g h =
      fst (SSet.boundary 1).toSSet Δ[2] ≫ (SSet.boundary 1).ι ≫ SSet.yonedaEquiv.symm
        ((monicKTracedNativeTriplePrescribedEdge F f g h).map
          (monicKTracedTripleZeroEvaluation (w := w) (z := z) F)).edge :=
  constantDiamondEdgeComparisonRealization_relative _ _ _ _ _

/-- BF 零段比較を、元の raw 比較問題の同じ零段の厳密な型で回収する。 -/
def monicKTracedTripleRawZeroComparison : EndpointFixedEdgeCylinder
    (((monicKTracedNativeTriplePrescribedEdge F f g h).map
      (kRawMappingProjection (F.obj w) (F.obj z))).map
        (RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) 0))
    (((monicKTracedCoherentTripleGeneratedEdge F f g h).map
      (kRawMappingProjection (F.obj w) (F.obj z))).map
        (RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) 0)) :=
  endpointFixedCylinderMapTransport (monicKTracedNativeTriplePrescribedEdge F f g h)
    (monicKTracedCoherentTripleGeneratedEdge F f g h) (kRawMappingProjection_zero _ _)
    (monicKTracedTripleZeroComparison F f g h)

/-- 元の raw 型への移送も、同じ全零段比較円柱を厳密に保持する。 -/
lemma monicKTracedTripleRawZeroComparison_h :
    (monicKTracedTripleRawZeroComparison F f g h).homotopy.h =
      (monicKTracedTripleZeroComparison F f g h).homotopy.h :=
  endpointFixedCylinderMapTransport_h _ _ _ _

/-- 元の全二三角形を保持する高次比較の指定面は、同じ raw 零段円柱そのもの。 -/
lemma monicKTracedTripleRawZeroComparison_realization :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 2) ≫
        monicKTracedTripleZeroComparisonRealization F f g h =
      (monicKTracedTripleRawZeroComparison F f g h).homotopy.h :=
  (monicKTracedTripleZeroComparisonRealization_comparison F f g h).trans
    (monicKTracedTripleRawZeroComparison_h F f g h).symm

end SerrePositivity.KST.SConstruction
