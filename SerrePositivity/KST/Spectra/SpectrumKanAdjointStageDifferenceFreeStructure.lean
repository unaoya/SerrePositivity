module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointStageDifferenceFreeMap
public import SerrePositivity.KST.Spectra.SquareEndpointFixed
public import SerrePositivity.KST.Spectra.PointedCotensorRelativeHomotopies

/-!
概要：両端を固定する同じ比較正方形から、自由区間値の段射の垂直な構造区間を作る。
方針：二端点全体での定数性を座標同型で移し、源制限・構造像の端点を照合する。
規約：自由境界射影に全区間で垂直。使われ方：全列区間の相対厳密化の構造入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right]

/-- 同じ比較正方形を、次段区間の制限と前段区間の構造像の実ホモトピーとして表示。 -/
def kanAdjointStageDifferenceStructureHomotopy (n : ℕ) :
    SSet.Homotopy
      (((kanAdjointStageDifference X Y φ j (n + 1)).path).pre (X.sigma n)).path
      ((PointedMapping.VerticalPath.basedPost
        (kanAdjointStageDifference X Y φ j n).path.suspension.forgetProjection
        ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path) where
  h := (kanAdjointStageDifferenceSquare X Y φ j n).h
  h₀ := kanAdjointStageDifferenceSquare_zero X Y φ j n
  h₁ := kanAdjointStageDifferenceSquare_one X Y φ j n
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 同じ構造正方形は、二端点の境界全体を元の始辺の値で固定する。 -/
lemma kanAdjointStageDifferenceStructureHomotopy_relative (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}.right ▷ (Δ[1] : SSet.{u}) ≫
      (kanAdjointStageDifferenceStructureHomotopy X Y φ j n).h =
    fst ((𝟙_ SSet.{u}) ⨿ (𝟙_ SSet.{u})) (Δ[1] : SSet.{u}) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.right ≫
        (((kanAdjointStageDifference X Y φ j (n + 1)).path).pre (X.sigma n)).path :=
  SquareAdjustment.fixed_endpoints (kanAdjointStageDifferenceStructureHomotopy X Y φ j n) _ _
    (kanAdjointStageDifferenceSquare_left_constant X Y φ j n)
    (kanAdjointStageDifferenceSquare_right_constant X Y φ j n)

/-- 同じ正方形から得る、両端境界射影に全区間で垂直な自由区間値の構造区間。 -/
def kanAdjointStageDifferenceFreeStructureInterval (n : ℕ) :
    PointedMapping.VerticalPath
      ((KanSequence.mappingPre _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion
        (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence))).app (n + 1))
      (X.sigma n ≫ kanAdjointStageDifferenceFreeMap X Y φ j (n + 1))
      (PointedSimplicialSet.circle.{u} ◁ kanAdjointStageDifferenceFreeMap X Y φ j n ≫
        (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).freePath.sigma n) :=
  (PointedCotensorCoordinates.relativeIntervalOfHomotopy _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.right
    (kanAdjointStageDifferenceStructureHomotopy X Y φ j n)
    (kanAdjointStageDifferenceStructureHomotopy_relative X Y φ j n)).changeEndpoints
      (kanAdjointStageDifferenceFreeMap_pre X Y φ j n).symm
      (kanAdjointStageDifferenceFreeMap_step X Y φ j n).symm

end SerrePositivity.KST.Spectra.RawSpectrumMapping
