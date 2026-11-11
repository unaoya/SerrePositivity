module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetNestedBoundColimit
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCorePoint
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridExtension
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.NerveBoundCocone

/-!
概要：比較格子の中央終点へ向かう八頂点の実余錐とその余極限性。
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

def IsExcisionGridPast (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u}) : Prop :=
  p.val.val.down.val.1.val + p.val.val.down.val.2.val ≤ 3

abbrev ExcisionGridPastIndex := {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} // IsExcisionGridPast p}

lemma excisionGridSeed_past (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u}) (hp : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridSeed p) :
    IsExcisionGridPast p := by
  exact hp.trans (by decide)

lemma excisionGridCorePoint_top (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u}) :
    p ≤ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint 2 2 := p.property

def excisionGridPastCocone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion IsExcisionGridPast.{u})) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_nerve_joinCocone_at_bound.{u}
    (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion IsExcisionGridPast.{u})) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint 2 2)
    (fun v ↦ excisionGridCorePoint_top (nerveEquiv v).val))

lemma excisionGridPastCocone_vertex : excisionGridPastCocone.{u}.vertex =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint 2 2) :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_nerve_joinCocone_at_bound.{u}
    (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion IsExcisionGridPast.{u})) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint 2 2)
    (fun v ↦ excisionGridCorePoint_top (nerveEquiv v).val))

lemma ExcisionGridExtension.past_cocone_colimit {X : SSet.{u}} [Quasicategory X]
    {G : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridExtension G z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone d.core excisionGridPastCocone) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isColimit_mapJoinCocone_of_poset_nested_canonical_bound _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridSeed
    IsExcisionGridPast excisionGridSeed_past (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint 2 2)
    (fun p _ ↦ excisionGridCorePoint_top p) excisionGridPastCocone
    excisionGridPastCocone_vertex d.core d.core_colimit

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
