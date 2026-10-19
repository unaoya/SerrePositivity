module

public import SerrePositivity.KST.Spectra.SequenceIntervalBoundary
public import SerrePositivity.KST.Spectra.SequenceRelativeTracedTriangles
public import SerrePositivity.KST.Spectra.SequenceParameterRelativeRectification

/-!
概要：両端の厳密な列射を同時に固定し、区間列を実構造三角形つきで厳密化する。
方針：自由区間の両端への制限 fibration の上で、相対帰納構成を行う。
規約：構造区間は両端固定の実区間を要求する。使われ方：全 Hom の区間の延長問題。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.KanSequence

/-- 同じ二つの厳密な列射を両端に持つ、全列の実区間。 -/
structure StrictInterval {X Y : KanSequence.{u}} (f g : Hom X Y) where
  hom : Hom X Y.freePath
  boundary : ∀ n, hom.app n ≫ (mappingPre freeBoundaryInclusion Y).app n =
    (intervalBoundaryPair f g).app n

/-- 全列区間の始点は、指定した同じ厳密な列射。 -/
lemma StrictInterval.start {X Y : KanSequence.{u}} {f g : Hom X Y}
    (H : StrictInterval f g) (n : ℕ) :
    H.hom.app n ≫ (freePathEvaluation Y 1).app n = f.app n := by
  have h := congrArg (· ≫ freeBoundaryHomStart (Y.level n).space) (H.boundary n)
  change (H.hom.app n ≫ PointedMapping.prePointed freeBoundaryInclusion _) ≫ _ =
    freeBoundaryHomPair (f.app n) (g.app n) ≫ freeBoundaryHomStart _ at h
  rw [freeBoundaryHomPair_start] at h
  have he : PointedMapping.prePointed freeBoundaryInclusion (Y.level n).space ≫
      freeBoundaryHomStart (Y.level n).space = (freePathEvaluation Y 1).app n := by
    change PointedMapping.prePointed freeBoundaryInclusion _ ≫
      (PointedMapping.prePointed freeBoundaryStart _ ≫ _) = _
    rw [← Category.assoc, PointedMapping.prePointed_comp, freeBoundaryStart_inclusion]
    rfl
  rw [Category.assoc, he] at h
  exact h

/-- 全列区間の終点も、指定した同じ厳密な列射。 -/
lemma StrictInterval.finish {X Y : KanSequence.{u}} {f g : Hom X Y}
    (H : StrictInterval f g) (n : ℕ) :
    H.hom.app n ≫ (freePathEvaluation Y 0).app n = g.app n := by
  have h := congrArg (· ≫ freeBoundaryHomEnd (Y.level n).space) (H.boundary n)
  change (H.hom.app n ≫ PointedMapping.prePointed freeBoundaryInclusion _) ≫ _ =
    freeBoundaryHomPair (f.app n) (g.app n) ≫ freeBoundaryHomEnd _ at h
  rw [freeBoundaryHomPair_end] at h
  have he : PointedMapping.prePointed freeBoundaryInclusion (Y.level n).space ≫
      freeBoundaryHomEnd (Y.level n).space = (freePathEvaluation Y 0).app n := by
    change PointedMapping.prePointed freeBoundaryInclusion _ ≫
      (PointedMapping.prePointed freeBoundaryEnd _ ≫ _) = _
    rw [← Category.assoc, PointedMapping.prePointed_comp, freeBoundaryEnd_inclusion]
    rfl
  rw [Category.assoc, he] at h
  exact h

variable {X Y : KanSequence.{u}} (hX : ∀ n, Mono (X.sigma n).right) (f g : Hom X Y)
  (k : ∀ n, (X.level n).space ⟶ (Y.freePath.level n).space)
  (hk : ∀ n, k n ≫ (mappingPre freeBoundaryInclusion Y).app n =
    (intervalBoundaryPair f g).app n)
  (h : ∀ n, PointedMapping.VerticalPath ((mappingPre freeBoundaryInclusion Y).app (n + 1))
    (X.sigma n ≫ k (n + 1)) (PointedSimplicialSet.circle.{u} ◁ k n ≫ Y.freePath.sigma n))

/-- 両端を固定する構造区間から、同じ両端を持つ全列の厳密な区間を構成する。 -/
def rectifyInterval : StrictInterval f g where
  hom := relativeTracedRectify hX (mappingPre freeBoundaryInclusion Y)
    (RawSpectrumMapping.mappingPre_level_horn_rlp freeBoundaryInclusion Y)
    (intervalBoundaryPair f g) k hk h
  boundary n := relativeTracedRectify_projection hX (mappingPre freeBoundaryInclusion Y)
    (RawSpectrumMapping.mappingPre_level_horn_rlp freeBoundaryInclusion Y)
    (intervalBoundaryPair f g) k hk h n

/-- 零段の元の区間全体を保持する。 -/
lemma rectifyInterval_zero : (rectifyInterval hX f g k hk h).hom.app 0 = k 0 := rfl

/-- 区間の変更そのものも、両端を固定する実垂直区間として保持する。 -/
def rectifyIntervalComparison (n : ℕ) :
    PointedMapping.VerticalPath ((mappingPre freeBoundaryInclusion Y).app n) (k n)
      ((rectifyInterval hX f g k hk h).hom.app n) :=
  relativeTracedRectifyComparison hX (mappingPre freeBoundaryInclusion Y)
    (RawSpectrumMapping.mappingPre_level_horn_rlp freeBoundaryInclusion Y)
    (intervalBoundaryPair f g) k hk h n

/-- 段間の構造三角形は、同じ両端への射影を全体で固定する。 -/
def rectifyIntervalTriangle (n : ℕ) :=
  relativeTracedComparison_triangle (X := X) (Y := Y.freePath)
    (Z := mapping freeIntervalBoundary Y) hX (mappingPre freeBoundaryInclusion Y)
    (RawSpectrumMapping.mappingPre_level_horn_rlp freeBoundaryInclusion Y)
    (intervalBoundaryPair f g) k hk h n

end SerrePositivity.KST.Spectra.KanSequence
