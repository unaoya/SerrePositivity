module
public import SerrePositivity.KST.SConstruction.TracedBFTripleRawBoundaryFaces
public import SerrePositivity.KST.SConstruction.FixedBoundaryPullback

/-! # 元の BF 比較辺の全段評価と同じ直通列制限
概要：元の BF 合成比較辺の各段を、同じ累積 raw 円柱の直通列制限として回収する。
方針：元の全 BF 射影の式と区間パラメータの厳密な等号を使う。
規約：正の全段の全区間を保持し、元の比較辺を選び直さない。
使われ方：累積相対補正を元の BF 辺の各段へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
local instance tracedCompositionStageSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の直通列点を固定して元の全比較区間だけを動かす同じ実パラメータ。 -/
def monicKTracedCompositionIntervalPoint :=
  intervalParameterPoint (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g)))

/-- 元の BF 比較辺の全段評価は、同じ元の全 raw 円柱の直通列制限そのもの。 -/
lemma monicKTracedSpectrumCompositionEdge_raw_evaluation (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedSpectrumCompositionEdge F f g).edge ≫
        kRawMappingProjection (F.obj x) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n =
      monicKTracedCompositionIntervalPoint f g ≫ (monicKPrismNativeRawComparison F f g).h ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n := by
  rw [monicKTracedSpectrumCompositionEdge_map, Category.assoc,
    ← Category.assoc (monicKPrismTracedBFCompositionBoundary F f g).h,
    monicKPrismTracedBFCompositionBoundary_projection]
  rw [← Category.assoc, ← Category.assoc, intervalParameterPoint_of_map]
  rfl

/-- 元の同じ全区間の各段は、累積補正済み段の同じ実制限を厳密に回収する。 -/
lemma monicKTracedSpectrumCompositionEdge_corrected_evaluation (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedSpectrumCompositionEdge F f g).edge ≫
        kRawMappingProjection (F.obj x) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n =
      monicKTracedCompositionIntervalPoint f g ≫
        (monicKPrismNativeCumulativeComparisonStage F f g n).val.h := by
  rw [monicKTracedSpectrumCompositionEdge_raw_evaluation, monicKPrismNativeRawComparison_evaluation]

end SerrePositivity.KST.SConstruction
