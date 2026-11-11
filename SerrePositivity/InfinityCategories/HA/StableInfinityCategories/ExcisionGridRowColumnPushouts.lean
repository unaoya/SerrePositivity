module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridRowColumnFaces

/-!
概要：三面の貼り合わせから残る大きな二四角形の押し出し性を得る。
方針：同じ実図式の貼り合わせ・全パラメーターの評価・普遍的な切断比較を使う。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma ExcisionGridExtension.row_outer_pushout {X : SSet.{u}} [Quasicategory X]
    {G : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridExtension G z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRowStrip ≫ d.full) 1 1) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_strip3_outer
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRowStrip 3 2 ≫ d.full)
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRowStrip_first]
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare, Category.assoc, d.middle_eq, d.core_eq] using
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_transpose _).mp d.upper_right_pushout
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRowStrip 3 0 ≫ d.full)
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRowStrip_second]
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare, Category.assoc, d.middle_eq, d.core_eq] using d.center_pushout
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRowStrip 0 0 ≫ d.full)
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridRowStrip_third]
    exact d.right_pushout

lemma ExcisionGridExtension.column_outer_pushout {X : SSet.{u}} [Quasicategory X]
    {G : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridExtension G z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridColumnStrip ≫ d.full) 1 1) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_strip3_outer
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridColumnStrip 3 2 ≫ d.full)
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridColumnStrip_first]
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare, Category.assoc, d.middle_eq, d.core_eq] using
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_transpose _).mp d.lower_right_pushout
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridColumnStrip 3 0 ≫ d.full)
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridColumnStrip_second]
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare, Category.assoc, d.middle_eq, d.core_eq] using
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_transpose _).mp d.center_pushout
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.strip3Square _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridColumnStrip 0 0 ≫ d.full)
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridColumnStrip_third]
    exact d.left_pushout

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
