module
public import SerrePositivity.KST.SConstruction.TracedBFCompositionStageSpans
public import SerrePositivity.KST.SConstruction.TriangleUpperFaceTransport

/-! # 元の全 span 三角形を保つ実 BF 段比較面への移送
概要：元の全各段 span 三角形を始端に保持し、比較面だけを元の実 BF 段辺へ移す。
方針：元の全累積補正を同じ三角形境界に貼り、時刻零固定の相対移送を実適用する。
規約：直接補正・合成補正の全二辺を全時刻固定し、元の全補正円柱を動く側面に回収する。
使われ方：正の段の第四辺 raw 比較を元の四つの二入力合成面から構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance correctedSpanSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の span 比較面から実 BF 段辺への、元の全補正円柱の始端表示だけを移す。 -/
def monicKTracedCompositionSpanBoundaryCorrection (n : ℕ) :=
  familyHomotopyEndpointTransport (monicKTracedCompositionStageCorrection F f g n)
    (monicKTracedCompositionOriginalSpan_comparison F f g n) rfl

/-- 始端の表示移送でも、元の同じ全累積補正円柱そのもの。 -/
lemma monicKTracedCompositionSpanBoundaryCorrection_h (n : ℕ) :
    (monicKTracedCompositionSpanBoundaryCorrection F f g n).h =
      (monicKTracedCompositionStageCorrection F f g n).h :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 元の span 比較面の全区間境界は、元の全補正の全時刻で厳密に固定する。 -/
lemma monicKTracedCompositionSpanBoundaryCorrection_relative (n : ℕ) :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedCompositionSpanBoundaryCorrection F f g n).h =
      fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫ stdSimplex.δ 0 ≫
        monicKTracedCompositionOriginalSpan F f g n := by
  rw [monicKTracedCompositionSpanBoundaryCorrection_h,
    monicKTracedCompositionStageCorrection_relative]
  exact congrArg (fun q => fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫ q)
    (monicKTracedCompositionOriginalSpan_comparison F f g n).symm

/-- 元の全 span 三角形と二固定辺、元の全補正を保持した実 BF 段辺への相対移送。 -/
def monicKTracedCompositionCorrectedSpanData (n : ℕ) :=
  triangleUpperFaceTransportData (monicKTracedCompositionOriginalSpan F f g n)
    (SSet.yonedaEquiv.symm (monicKTracedSpectrumCompositionEdge F f g).edge ≫
      kRawMappingProjection (F.obj x) (F.obj z) ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n)
    (monicKTracedCompositionSpanBoundaryCorrection F f g n)
    (monicKTracedCompositionSpanBoundaryCorrection_relative F f g n)

/-- 元の直接補正・合成補正と実 BF 段辺を三辺に持つ実全三角形。 -/
def monicKTracedCompositionCorrectedSpan (n : ℕ) :=
  (monicKTracedCompositionCorrectedSpanData F f g n).val

/-- 元の実 BF 比較辺の全 raw 段評価を、新三角形の比較面に厳密に回収する。 -/
lemma monicKTracedCompositionCorrectedSpan_comparison (n : ℕ) :
    stdSimplex.δ 0 ≫ monicKTracedCompositionCorrectedSpan F f g n =
      SSet.yonedaEquiv.symm (monicKTracedSpectrumCompositionEdge F f g).edge ≫
        kRawMappingProjection (F.obj x) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n :=
  (monicKTracedCompositionCorrectedSpanData F f g n).face_zero

/-- 元の直接補正の全区間は、新三角形の同じ第一面にそのまま保持する。 -/
lemma monicKTracedCompositionCorrectedSpan_first (n : ℕ) :
    stdSimplex.δ 2 ≫ monicKTracedCompositionCorrectedSpan F f g n =
      monicKTracedCompositionIntervalPoint f g ≫
        (monicKPrismNativeDirectCorrectionData F f g n).homotopy.h :=
  (monicKTracedCompositionCorrectedSpanData F f g n).face_two.trans
    (monicKTracedCompositionOriginalSpan_first F f g n)

/-- 元の合成補正の全区間も、新三角形の同じ合成面にそのまま保持する。 -/
lemma monicKTracedCompositionCorrectedSpan_composite (n : ℕ) :
    stdSimplex.δ 1 ≫ monicKTracedCompositionCorrectedSpan F f g n =
      monicKTracedCompositionIntervalPoint f g ≫
        (monicKPrismNativeCompositeCorrectionData F f g n).homotopy.h :=
  (monicKTracedCompositionCorrectedSpanData F f g n).face_one.trans
    (monicKTracedCompositionOriginalSpan_composite F f g n)

/-- 元の同じ全 span 三角形から新三角形へ出る、元の全補正を側面に持つ実比較。 -/
def monicKTracedCompositionCorrectedSpanComparison (n : ℕ) :=
  (monicKTracedCompositionCorrectedSpanData F f g n).comparison

/-- 元の全二単体を全比較の始端に厳密に保持する。 -/
lemma monicKTracedCompositionCorrectedSpanComparison_source (n : ℕ) :
    SSet.ι₀ ≫ (monicKTracedCompositionCorrectedSpanComparison F f g n).h =
      monicKTracedCompositionOriginalSpan F f g n :=
  (monicKTracedCompositionCorrectedSpanComparison F f g n).h₀

/-- 動く比較面の側面全体は、元の同じ全累積補正円柱そのもの。 -/
lemma monicKTracedCompositionCorrectedSpanComparison_comparison (n : ℕ) :
    (stdSimplex.δ 0 ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedCompositionCorrectedSpanComparison F f g n).h =
      (monicKTracedCompositionStageCorrection F f g n).h :=
  (monicKTracedCompositionCorrectedSpanData F f g n).comparison_zero.trans
    (monicKTracedCompositionSpanBoundaryCorrection_h F f g n)

/-- 元の全直接補正面を全比較時刻で厳密に固定する。 -/
lemma monicKTracedCompositionCorrectedSpanComparison_first (n : ℕ) :
    (stdSimplex.δ 2 ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedCompositionCorrectedSpanComparison F f g n).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ monicKTracedCompositionIntervalPoint f g ≫
        (monicKPrismNativeDirectCorrectionData F f g n).homotopy.h :=
  (monicKTracedCompositionCorrectedSpanData F f g n).comparison_two.trans
    (congrArg (fst (Δ[1] : SSet.{u}) Δ[1] ≫ ·)
      (monicKTracedCompositionOriginalSpan_first F f g n))

/-- 元の全合成補正面も全比較時刻で厳密に固定する。 -/
lemma monicKTracedCompositionCorrectedSpanComparison_composite (n : ℕ) :
    (stdSimplex.δ 1 ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedCompositionCorrectedSpanComparison F f g n).h =
      fst (Δ[1] : SSet.{u}) Δ[1] ≫ monicKTracedCompositionIntervalPoint f g ≫
        (monicKPrismNativeCompositeCorrectionData F f g n).homotopy.h :=
  (monicKTracedCompositionCorrectedSpanData F f g n).comparison_one.trans
    (congrArg (fst (Δ[1] : SSet.{u}) Δ[1] ≫ ·)
      (monicKTracedCompositionOriginalSpan_composite F f g n))

end SerrePositivity.KST.SConstruction
