module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridUpperSeedCorner

/-!
概要：上面の実余錐と native 下方余錐の厳密な比較。
方針：元の射影・実余錐・全単体の頂点式を保持して比較する。
規約：一般安定性の結論は先取りしない。使われ方：HA 1.4.2.15 の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def excisionGridUpperRectangleCocone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (nerveMap
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerProjection _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridSeed (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint.{u} 1 2)) ≫
        nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSeedInclusion) := by
  let d := (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.pastingCocone _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridUpperRectangle).restrict
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridUpperSeedCornerIso.hom
  refine ⟨d.val, d.property.trans ?_⟩
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridUpperSeedCornerIso_projection

lemma excisionGridUpperRectangleCocone_vertex :
    excisionGridUpperRectangleCocone.{u}.vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint 1 2) := by
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  fin_cases i
  apply Subtype.ext
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridUpperRectangleCocone_val :
    excisionGridUpperRectangleCocone.{u}.val =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridSeed (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint 1 2)).val := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveCocone_val_eq_of_vertex
  rw [excisionGridUpperRectangleCocone_vertex, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone_vertex]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
