module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCenterSquare
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingPiZero

/-!
概要：中央の実余錐と標準正方形の余錐を同じ頂点で同定する。
方針：同じ実図式の native 余錐と頂点を保持して比較する。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の中央面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P : Type u} [PartialOrder P]

def excisionGridCenterCocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCenterSquare.{u}) := by
  let d := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridPastCocone.restrict
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridPastIndex.{u})
      (fun v ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridCenterSpan (nerveEquiv v))).ι).restrict
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCenterSpanShapeIso.hom
  exact ⟨d.val, d.property.trans _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCenterSpanShapeIso_projection⟩

lemma excisionGridCenterCocone_vertex : excisionGridCenterCocone.{u}.vertex =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint 2 2) := by
  change ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridPastCocone.restrict _).restrict _).vertex = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridPastCocone_vertex]

lemma excisionGridCenterCocone_val : excisionGridCenterCocone.{u}.val =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCenterSquare).val := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveCocone_val_eq_of_vertex
  rw [excisionGridCenterCocone_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pushoutCocone_vertex]
  symm
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  fin_cases i
  apply Subtype.ext
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> decide

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
