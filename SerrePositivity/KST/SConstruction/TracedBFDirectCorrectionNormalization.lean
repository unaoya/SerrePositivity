module
public import SerrePositivity.KST.SConstruction.MonicKPrismCanonicalDirectCorrection
public import SerrePositivity.KST.SConstruction.TracedBFCompositionStageTriangles
public import SerrePositivity.KST.SConstruction.FixedBoundaryPullback

/-! # 元の直接補正辺を同じ単一合成射の全円柱へ合わせる
概要：二入力の元の直接補正を、同じ単一合成射の円柱へ全端点固定で実比較する。
方針：元の全合成木の比較を直通列点へ制限し、同じ単一射の実パラメータを回収する。
規約：元の二円柱全体を両端に保持する。各段の合成木・全 trace は元の同じ入力。
使われ方：三入力の左右結合で共有する直接補正辺を照合して消去する。
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
local instance directNormalizationSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y)

/-- 元の単一射の全補正円柱を、その同じ直通列点へ制限した全区間。 -/
def monicKTracedUnaryCorrectionAtPoint (n : ℕ) :=
  intervalParameterPoint (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f))) ≫
    (monicKPrismUnaryCorrectionData F f n).homotopy.h

variable {z : I} (g : y ⟶ z)

/-- 元の二入力の直接補正円柱を、元の同じ直通列点へ制限した全区間。 -/
def monicKTracedDirectCorrectionAtPoint (n : ℕ) :=
  monicKTracedCompositionIntervalPoint f g ≫
    (monicKPrismNativeDirectCorrectionData F f g n).homotopy.h

/-- 先に合成して引き戻した円柱の直通列制限は、同じ元の単一合成射の全円柱。 -/
lemma monicKPrismNativeCanonicalDirectData_point (n : ℕ) :
    monicKTracedCompositionIntervalPoint f g ≫
        (monicKPrismNativeCanonicalDirectData F f g n).homotopy.h =
      monicKTracedUnaryCorrectionAtPoint F (f ≫ g) n := by
  rw [monicKPrismNativeCanonicalDirectData_h, ← Category.assoc]
  change (pointParameterMap (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g)))
    (Δ[1] : SSet.{u}) ≫ (nerveMap (compositionStringComposite f g) ▷ (Δ[1] : SSet.{u}))) ≫ _ = _
  rw [pointParameterMap_post_point, compositionStringComposite_direct]
  rfl

/-- 元の直接補正から、同じ元の単一合成射の円柱への全端点固定実比較。 -/
def monicKTracedDirectCorrectionNormalization (n : ℕ) :=
  familyHomotopyEndpointTransport
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (monicKPrismNativeDirectCanonicalComparison F f g n)
      (monicKTracedCompositionIntervalPoint f g)) rfl
    (monicKPrismNativeCanonicalDirectData_point F f g n)

/-- 元の全合成木の比較を、その同じ直通列点へ制限した全実写像を保持する。 -/
lemma monicKTracedDirectCorrectionNormalization_h (n : ℕ) :
    (monicKTracedDirectCorrectionNormalization F f g n).h =
      (monicKTracedCompositionIntervalPoint f g ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismNativeDirectCanonicalComparison F f g n).h :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 元の全区間境界を、直接補正の比較の全時刻で厳密に固定する。 -/
lemma monicKTracedDirectCorrectionNormalization_relative (n : ℕ) :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedDirectCorrectionNormalization F f g n).h =
      fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫
        monicKTracedDirectCorrectionAtPoint F f g n := by
  rw [monicKTracedDirectCorrectionNormalization, familyHomotopyEndpointTransport_h]
  exact fixedBoundaryHomotopy_intervalPoint _ _
    (monicKPrismNativeDirectCanonicalComparison_boundary F f g n)

/-- 零段の全正規化比較は、元の合成射の同じ定数写像を全時刻で保持する。 -/
lemma monicKTracedDirectCorrectionNormalization_zero :
    (monicKTracedDirectCorrectionNormalization F f g 0).h =
      SSet.const (Spectra.PointedMapping.familyVertex
        (monicKToRawLevelMap (F.map (f ≫ g)) 0)) := by
  rw [monicKTracedDirectCorrectionNormalization_h,
    monicKPrismNativeDirectCanonicalComparison_zero, whiskerRight_fst_assoc,
    monicKPrismNativeDirectCorrectionData_zero]
  simp only [SSet.comp_const]

/-- 実 BF 段三角形の元の第一辺から、同じ単一合成射の円柱への全実比較。 -/
def monicKTracedCompositionStageFirstNormalization (n : ℕ) :=
  familyHomotopyEndpointTransport (monicKTracedDirectCorrectionNormalization F f g n)
    (monicKTracedCompositionStageTriangleData_first F f g n) rfl

/-- 実三角形の第一辺の表示へ移しても、元の同じ比較円柱全体を保持する。 -/
lemma monicKTracedCompositionStageFirstNormalization_h (n : ℕ) :
    (monicKTracedCompositionStageFirstNormalization F f g n).h =
      (monicKTracedDirectCorrectionNormalization F f g n).h :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 元の実三角形の第一辺の全区間境界を、全比較時刻で厳密に固定する。 -/
lemma monicKTracedCompositionStageFirstNormalization_relative (n : ℕ) :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedCompositionStageFirstNormalization F f g n).h =
      fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm (monicKTracedCompositionStageTriangleData F f g n).first.edge := by
  rw [monicKTracedCompositionStageFirstNormalization_h,
    monicKTracedDirectCorrectionNormalization_relative]
  exact congrArg (fun q => fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫ q)
    (monicKTracedCompositionStageTriangleData_first F f g n).symm

end SerrePositivity.KST.SConstruction
