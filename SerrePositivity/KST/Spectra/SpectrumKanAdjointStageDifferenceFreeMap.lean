module

public import SerrePositivity.KST.Spectra.SpectrumKanAdjointStageDifferenceBoundary
public import SerrePositivity.KST.Spectra.PointedFreeIntervalBoundaryMap
public import SerrePositivity.KST.Spectra.PointedCotensorFamilyStructure

/-!
概要：厳密な終点間の同じ段比較区間を、自由区間を値とする段射へ移す。
方針：全関数複体の座標同型と端点・源制限・構造像の厳密自然性を使う。
規約：両端境界族を厳密に保持。使われ方：全列区間の相対厳密化の段入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A B : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence) (j : B ⟶ A) [Mono j.right]

/-- 同じ段比較区間を自由区間値の射として表示する。 -/
def kanAdjointStageDifferenceFreeMap (n : ℕ) :
    (X.level n).space ⟶
      ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).freePath.level
        n).space :=
  (kanAdjointStageDifference X Y φ j n).path.freeMap

/-- 自由区間値へ移した各段は、二つの元の厳密列射の同じ両端境界族を持つ。 -/
lemma kanAdjointStageDifferenceFreeMap_boundary (n : ℕ) :
    kanAdjointStageDifferenceFreeMap X Y φ j n ≫
      (KanSequence.mappingPre _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion
        (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence))).app n =
    (KanSequence.intervalBoundaryPair (kanAdjointRelativeTracedParameterHom X Y φ j)
      (kanAdjointTracedUnitParameterHom X Y φ)).app n :=
  (kanAdjointStageDifference X Y φ j n).path.freeMap_boundary

/-- 次段の比較区間の源制限を移すと、同じ自由区間値の次段射の源制限。 -/
lemma kanAdjointStageDifferenceFreeMap_pre (n : ℕ) :
    PointedCotensorCoordinates.family
      (((kanAdjointStageDifference X Y φ j (n + 1)).path).pre (X.sigma n)).path =
    X.sigma n ≫ kanAdjointStageDifferenceFreeMap X Y φ j (n + 1) := by
  exact (PointedCotensorCoordinates.family_source (X.sigma n)
    (kanAdjointStageDifference X Y φ j (n + 1)).path.path).symm

/-- 前段比較区間の構造像を移すと、同じ自由区間値の前段射の構造像。 -/
lemma kanAdjointStageDifferenceFreeMap_step (n : ℕ) :
    PointedCotensorCoordinates.family
      ((PointedMapping.VerticalPath.basedPost
        (kanAdjointStageDifference X Y φ j n).path.suspension.forgetProjection
        ((KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).sigma n)).path) =
    PointedSimplicialSet.circle.{u} ◁ kanAdjointStageDifferenceFreeMap X Y φ j n ≫
      (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)).freePath.sigma n := by
  rw [PointedMapping.VerticalPath.suspension_basedPost_path]
  exact (PointedCotensorCoordinates.family_step (Δ[1] : SSet.{u}) X
    (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)) n
    (kanAdjointStageDifference X Y φ j n).path.path).symm

end SerrePositivity.KST.Spectra.RawSpectrumMapping
