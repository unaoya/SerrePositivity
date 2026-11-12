module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridRightSpanProjection

/-!
概要：同じ (3,2) を頂点とする実余錐と標準正方形の余錐を同定する。
方針：同じ実図式の native 余錐・頂点・二辺を保持して比較する。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の外側の面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def excisionGridRightCocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRightSquare.{u}) := by
  let d := ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridPoint32).restrict
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridRightLowerIndex.{u})
      (fun v ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridRightSpan (nerveEquiv v))).ι).restrict
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRightSpanShapeIso.hom
  exact ⟨d.val, d.property.trans _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRightSpanShapeIso_projection⟩

lemma excisionGridRightCocone_vertex : excisionGridRightCocone.{u}.vertex =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridPoint32 := by
  change (((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridPoint32).restrict
    _).restrict _).vertex = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone_vertex]

lemma excisionGridRightCocone_val : excisionGridRightCocone.{u}.val =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRightSquare).val := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveCocone_val_eq_of_vertex
  rw [excisionGridRightCocone_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pushoutCocone_vertex]
  symm
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  fin_cases i
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> decide

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
