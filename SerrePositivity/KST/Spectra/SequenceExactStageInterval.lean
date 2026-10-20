module

public import SerrePositivity.KST.Spectra.SequenceIntervalRectification
public import SerrePositivity.KST.Spectra.PointedFreeIntervalBoundaryMap
public import SerrePositivity.KST.Spectra.PointedCotensorFamilyStructure
public import SerrePositivity.KST.Spectra.PointedBasedPathDifference

/-!
概要：段の実区間が構造経路の厳密一致を満たすとき、同じ区間全体を全列区間へ束ねる。
方針：各段を自由区間値へ交換し、元の辺の構造等式から実際の列射を構成する。
規約：新しい充填を選ばず元の両端を保持。使われ方：全 Hom から来る源単位区間。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.KanSequence

/-- 構造条件を辺全体で厳密に満たす元の段区間を、両端固定の同じ全列区間へ束ねる。 -/
def strictIntervalOfExactStagePaths (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (f g : Hom X.toKanSequence Y)
    (P : ∀ n, PointedMapping.VerticalPath (PointedObject.toPoint (Y.level n).space)
      (f.app n) (g.app n))
    (hP : ∀ n, ((P (n + 1)).pre (X.sigma n)).path =
      ((P n).suspension.forgetProjection.basedPost (Y.sigma n)).path) : StrictInterval f g where
  hom := {
    app n := (P n).freeMap
    comm n := by
      have hs := PointedCotensorCoordinates.family_step (Δ[1] : SSet.{u}) X Y n (P n).path
      have hp := congrArg PointedCotensorCoordinates.family (hP n)
      rw [PointedMapping.VerticalPath.suspension_basedPost_path] at hp
      have hr := PointedCotensorCoordinates.family_source (X.sigma n) (P (n + 1)).path
      exact hs.trans (hp.symm.trans hr.symm) }
  boundary n := (P n).freeMap_boundary

end SerrePositivity.KST.Spectra.KanSequence
