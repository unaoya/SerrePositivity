module

public import SerrePositivity.KST.Spectra.PointedCotensorIntervalEndpoints
public import SerrePositivity.KST.Spectra.SequenceIntervalBoundary

/-!
概要：元の実区間を自由区間へ移した射が、指定した両端の境界族へ厳密に制限される。
方針：二端点による境界 Hom の外延性を使う。
規約：境界全体の射の等式。使われ方：全列区間の相対厳密化の境界入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra

/-- 自由境界への制限後の終点評価は、元の自由区間の終点評価。 -/
lemma freeBoundary_restrict_end (E : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion E ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomEnd E =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint E 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomEnd, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp,
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryEnd_inclusion]
  rfl

/-- 自由境界への制限後の始点評価も、元の自由区間の始点評価。 -/
lemma freeBoundary_restrict_start (E : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion E ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomStart E =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint E 1 := by
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryHomStart, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp,
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryStart_inclusion]
  rfl

/-- 自由区間へ移した実区間は、元の二つの射を束ねた同じ境界族を持つ。 -/
lemma PointedMapping.VerticalPath.freeMap_boundary {T E : PointedSimplicialSet.{u}}
    {f g : T ⟶ E} (P : PointedMapping.VerticalPath (PointedObject.toPoint E) f g) :
    P.freeMap ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion E = freeBoundaryHomPair f g := by
  apply freeBoundaryHom_hom_ext
  · rw [Category.assoc, freeBoundary_restrict_end, freeBoundaryHomPair_end, P.freeMap_finish]
  · rw [Category.assoc, freeBoundary_restrict_start, freeBoundaryHomPair_start, P.freeMap_start]

end SerrePositivity.KST.Spectra
