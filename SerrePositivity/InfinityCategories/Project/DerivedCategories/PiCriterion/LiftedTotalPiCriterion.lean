module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.UniverseShape
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.TotalPiCriterion

/-!
概要：小さい底と大きい空間値を持つ元の余錐にも、全空間比較の π 判定を適用する。
方針：底の厳密な持ち上げ同型による制限と、同宇宙の比較判定を合成する。
規約：元の余錐の native 余極限性を判定し、余錐を仮定として取り替えない。
使われ方：w = max (u+1) v における κ-filtered poset 上の最終判定の入力。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion

/-- 宇宙を分離した元の余錐の余極限性は、持ち上げた全空間比較の π 判定と同値。 -/
lemma isColimitCone_iff_liftedTotalPiCriterion {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{max u v + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max u v})
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.KanMapPiCriterion (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.totalValueComparison (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.liftedBaseDiagram.{u, v} F)
        (c.restrict (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.liftedBaseShapeIso.{u, v} B).hom)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.isColimitCone_iff_liftedBase_restrict c).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.isColimitCone_iff_totalPiCriterion (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.liftedBaseDiagram.{u, v} F)
      (c.restrict (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.liftedBaseShapeIso.{u, v} B).hom))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
