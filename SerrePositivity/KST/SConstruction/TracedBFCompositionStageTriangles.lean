module
public import SerrePositivity.KST.SConstruction.TracedBFCompositionCorrectedSpans
public import SerrePositivity.KST.SConstruction.TriangleUpperEdgeData

/-! # 元の直接補正と実 BF 段辺の同じ実合成三角形
概要：全各段で、元の直接補正・実 BF 比較辺・元の合成補正を持つ実合成三角形を構成する。
方針：相対移送済みの同じ全 span 三角形を、実 BF 段辺を上辺に持つ合成表示へ移す。
規約：元の全二単体と両元の補正区間を厳密に保持する。合成類だけのデータにしない。
使われ方：正の段の第四辺 raw 比較で、四つの元の二入力合成面を照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open scoped Simplicial
local instance tracedStageTriangleSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の BF 比較辺を同じ raw 射影の指定段へ写した同じ全実辺。 -/
def monicKTracedCompositionRawStageEdge (n : ℕ) :=
  ((monicKTracedSpectrumCompositionEdge F f g).map (kRawMappingProjection (F.obj x) (F.obj z))).map
    (RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n)

/-- 段辺全体は、元の同じ BF 比較辺の全 raw 段評価そのもの。 -/
lemma monicKTracedCompositionRawStageEdge_map (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedCompositionRawStageEdge F f g n).edge =
      SSet.yonedaEquiv.symm (monicKTracedSpectrumCompositionEdge F f g).edge ≫
        kRawMappingProjection (F.obj x) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n := by
  exact (SSet.yonedaEquiv_symm_comp
    ((monicKTracedSpectrumCompositionEdge F f g).map
      (kRawMappingProjection (F.obj x) (F.obj z))).edge
    (RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x))
      (kKanSequence (F.obj z)) n)).symm.trans
      ((congrArg (· ≫ RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x))
        (kKanSequence (F.obj z)) n)
        (SSet.yonedaEquiv_symm_comp (monicKTracedSpectrumCompositionEdge F f g).edge
          (kRawMappingProjection (F.obj x) (F.obj z))).symm).trans (Category.assoc _ _ _))

/-- 実 BF 段辺と元の直接補正・合成補正を持つ、元の全 span 三角形の同じ合成表示。 -/
def monicKTracedCompositionStageTriangleData (n : ℕ) :=
  triangleUpperEdgeData (monicKTracedCompositionRawStageEdge F f g n)
    (monicKTracedCompositionCorrectedSpan F f g n)
    ((monicKTracedCompositionCorrectedSpan_comparison F f g n).trans
      (monicKTracedCompositionRawStageEdge_map F f g n).symm)

/-- 全実合成三角形は、元の相対移送済み span 二単体そのもの。 -/
lemma monicKTracedCompositionStageTriangleData_realization (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedCompositionStageTriangleData F f g n).triangle.simplex =
      monicKTracedCompositionCorrectedSpan F f g n :=
  (monicKTracedCompositionStageTriangleData F f g n).realization_eq

/-- 第一実辺の全区間は、元の直接補正円柱の同じ直通列制限そのもの。 -/
lemma monicKTracedCompositionStageTriangleData_first (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedCompositionStageTriangleData F f g n).first.edge =
      monicKTracedCompositionIntervalPoint f g ≫
        (monicKPrismNativeDirectCorrectionData F f g n).homotopy.h :=
  (monicKTracedCompositionStageTriangleData F f g n).first_map.trans
    (monicKTracedCompositionCorrectedSpan_first F f g n)

/-- 合成実辺の全区間も、元の合成補正円柱の同じ直通列制限そのもの。 -/
lemma monicKTracedCompositionStageTriangleData_direct (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedCompositionStageTriangleData F f g n).direct.edge =
      monicKTracedCompositionIntervalPoint f g ≫
        (monicKPrismNativeCompositeCorrectionData F f g n).homotopy.h :=
  (monicKTracedCompositionStageTriangleData F f g n).direct_map.trans
    (monicKTracedCompositionCorrectedSpan_composite F f g n)

/-- 同じ元の実三角形から、実 BF 段辺と両元の補正の合成関係を回収する。 -/
lemma monicKTracedCompositionStageTriangleData_comp (n : ℕ) :
    SSet.HomotopyCategory.homMk (monicKTracedCompositionStageTriangleData F f g n).first ≫
        SSet.HomotopyCategory.homMk (monicKTracedCompositionRawStageEdge F f g n) =
      SSet.HomotopyCategory.homMk (monicKTracedCompositionStageTriangleData F f g n).direct :=
  SSet.HomotopyCategory.homMk_comp_homMk
    (monicKTracedCompositionStageTriangleData F f g n).triangle

end SerrePositivity.KST.SConstruction
