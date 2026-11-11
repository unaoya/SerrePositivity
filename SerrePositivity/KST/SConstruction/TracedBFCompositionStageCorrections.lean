module
public import SerrePositivity.KST.SConstruction.MonicKPrismRawStageCorrections
public import SerrePositivity.KST.SConstruction.TracedBFCompositionStageEvaluation

/-! # 元の全 BF 合成比較辺と各段の元の実比較を結ぶ
概要：元の各段比較を、同じ BF 比較辺の段評価へ結ぶ全端点固定円柱を構成する。
方針：元の全累積補正を同じ直通列点へ制限し、終端の表示だけを厳密に合わせる。
規約：正の全段で元の補正全体を保持する。零段の補正は全時刻で元の定数円柱。
使われ方：正の段の第四辺比較を、元の合成 span 三角形と raw 高次 prism へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories Spectra.PointedMapping
open scoped Simplicial
local instance tracedStageCorrectionSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の直通列点に制限した、補正前の同じ各段比較区間。 -/
def monicKTracedCompositionOriginalStage (n : ℕ) :=
  monicKTracedCompositionIntervalPoint f g ≫ (monicKPrismNativeLevelComparison F f g n).h

/-- 元の補正前の段比較から、同じ BF 比較辺の raw 段評価への全実補正。 -/
def monicKTracedCompositionStageCorrection (n : ℕ) :=
  familyHomotopyEndpointTransport
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (monicKPrismNativeRawStageCorrection F f g n)
      (monicKTracedCompositionIntervalPoint f g)) rfl
    (monicKTracedSpectrumCompositionEdge_raw_evaluation F f g n).symm

/-- 終端の表示移送でも、元の同じ累積二次元補正の全直通列制限そのもの。 -/
lemma monicKTracedCompositionStageCorrection_h (n : ℕ) :
    (monicKTracedCompositionStageCorrection F f g n).h =
      (monicKTracedCompositionIntervalPoint f g ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismNativeCumulativeComparisonStage F f g n).correction.h := by
  rw [monicKTracedCompositionStageCorrection, familyHomotopyEndpointTransport_h]
  change _ ≫ (monicKPrismNativeRawStageCorrection F f g n).h = _
  rw [monicKPrismNativeRawStageCorrection_h]

/-- 各段比較の元の全区間境界は、補正の全時刻で厳密に固定する。 -/
lemma monicKTracedCompositionStageCorrection_relative (n : ℕ) :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedCompositionStageCorrection F f g n).h =
      fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫
        monicKTracedCompositionOriginalStage F f g n := by
  rw [monicKTracedCompositionStageCorrection, familyHomotopyEndpointTransport_h]
  exact fixedBoundaryHomotopy_intervalPoint _ _
    (monicKPrismNativeRawStageCorrection_boundary F f g n)

/-- 元の各段比較全体を、同じ二次元補正の始端に厳密に保持する。 -/
lemma monicKTracedCompositionStageCorrection_source (n : ℕ) :
    SSet.ι₀ ≫ (monicKTracedCompositionStageCorrection F f g n).h =
      monicKTracedCompositionOriginalStage F f g n :=
  (monicKTracedCompositionStageCorrection F f g n).h₀

/-- 同じ BF 比較辺の全段評価を、同じ二次元補正の終端に厳密に回収する。 -/
lemma monicKTracedCompositionStageCorrection_target (n : ℕ) :
    SSet.ι₁ ≫ (monicKTracedCompositionStageCorrection F f g n).h =
      SSet.yonedaEquiv.symm (monicKTracedSpectrumCompositionEdge F f g).edge ≫
        kRawMappingProjection (F.obj x) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n :=
  (monicKTracedCompositionStageCorrection F f g n).h₁

/-- 零段の全補正は、元の同じ段比較を全時刻で固定する定数円柱。 -/
lemma monicKTracedCompositionStageCorrection_zero :
    (monicKTracedCompositionStageCorrection F f g 0).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ monicKTracedCompositionOriginalStage F f g 0 := by
  rw [monicKTracedCompositionStageCorrection, familyHomotopyEndpointTransport_h]
  change _ ≫ (monicKPrismNativeRawStageCorrection F f g 0).h = _
  rw [monicKPrismNativeRawStageCorrection_zero, whiskerRight_fst_assoc]
  rfl

/-- 零段の同じ二次元補正全体は、元の合成射の同じ定数写像。 -/
lemma monicKTracedCompositionStageCorrection_zero_constant :
    (monicKTracedCompositionStageCorrection F f g 0).h =
      SSet.const (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) 0)) := by
  rw [monicKTracedCompositionStageCorrection_zero, monicKTracedCompositionOriginalStage,
    monicKPrismNativeLevelComparison_zero]
  simp only [SSet.comp_const]

end SerrePositivity.KST.SConstruction
