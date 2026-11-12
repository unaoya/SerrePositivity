module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridOuterDiagram

/-!
概要：full 格子の四面から元の終点を始点とする外側の押し出し性を得る。
方針：実際の長方形の貼り合わせと同じ図式の評価を使う。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma ExcisionGridExtension.final_outer_pushout {X : SSet.{u}} [Quasicategory X]
    {G : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridExtension G z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridOuterDiagram ≫ d.full) 1 1) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_grid22_outer
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridOuterDiagram 2 2 ≫ d.full)
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridOuterDiagram_lowerLeft]
    simpa only [Category.assoc, d.middle_eq, d.core_eq] using d.center_pushout
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridOuterDiagram 0 2 ≫ d.full)
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridOuterDiagram_lowerRight]
    exact d.right_pushout
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridOuterDiagram 2 0 ≫ d.full)
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridOuterDiagram_upperLeft, Category.assoc]
    exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_transpose _).mp d.left_pushout
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.grid22Face _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridOuterDiagram 0 0 ≫ d.full)
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridOuterDiagram_upperRight]
    exact d.final_pushout

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
