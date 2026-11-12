module

public import SerrePositivity.KST.Spectra.LoopPathFiber
public import SerrePositivity.KST.Spectra.PointedCofiberUniversal
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.FreeIntervalBoundary
public import SerrePositivity.KST.Spectra.PointedZeroMapping

/-!
概要：二端点を潰した円の loop から path への制限は、終点評価で零となる。
方針：cofiber の商の零合成を内部 Hom の反変合成へ移す。
規約：点つき射の厳密な零合成。使われ方：BF loop から native な引き戻しへの普遍射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
namespace SerrePositivity.KST.Spectra

/-- 内部 Hom の源の零射による制限は零射。 -/
lemma PointedMapping.prePointed_zero (A B Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (0 : A ⟶ B) Y = 0 := by
  let T := PointedObject.basedHom (PointedObject.point : PointedSimplicialSet.{u}) Y
  have : IsIso T.hom := isIso_of_isTerminal isTerminalTensorUnit (homPointIsTerminal Y) _
  have hz : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.toPoint A) Y = 0 :=
    PointedZeroMapping.hom_eq_zero T _ _
  rw [← PointedObject.toPoint_comp_fromPoint A B, ← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp, hz,
    comp_zero]

/-- 円への商による制限は終点で零となる。 -/
lemma endpointLoop_pathEndpoint_zero (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u}) Y ≫
      pathEndpoint Y = 0 := by
  unfold pathEndpoint
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp, pointedCofiberProjection_zero,
    PointedMapping.prePointed_zero, zero_comp]

end SerrePositivity.KST.Spectra
