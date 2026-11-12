module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridLowerSeedCorner

/-!
概要：同じ格子長方形の余錐と native 下方余錐を厳密に比較する。
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
variable {P : Type u} [PartialOrder P]

def excisionGridLowerRectangleCocone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (nerveMap
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerProjection _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridSeed (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint.{u} 2 1)) ≫
        nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSeedInclusion) := by
  let d := (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.pastingCocone _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridLowerRectangle).restrict
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridLowerSeedCornerIso.hom
  refine ⟨d.val, d.property.trans ?_⟩
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridLowerSeedCornerIso_projection

lemma excisionGridLowerRectangleCocone_vertex :
    excisionGridLowerRectangleCocone.{u}.vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint 2 1) := by
  apply CategoryTheory.nerve.ext_of_isThin
  funext i
  fin_cases i
  apply Subtype.ext
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> decide

lemma excisionGridLowerRectangleCocone_val :
    excisionGridLowerRectangleCocone.{u}.val =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridSeed (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint 2 1)).val := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveCocone_val_eq_of_vertex
  rw [excisionGridLowerRectangleCocone_vertex, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerCocone_vertex]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
