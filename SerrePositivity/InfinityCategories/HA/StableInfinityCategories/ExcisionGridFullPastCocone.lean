module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetNestedBoundColimit
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridExtension
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.NerveBoundCocone

/-!
概要：最終 (3,3) へ向かう十三頂点の実余錐の余極限性。
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
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

abbrev excisionGridPoint33 : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} := ULift.up ⟨(3, 3), by decide⟩

def IsExcisionGridFullPast (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u}) : Prop :=
  p.down.val.1.val + p.down.val.2.val ≤ 5

abbrev ExcisionGridFullPastIndex := {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} // IsExcisionGridFullPast p}

lemma excisionGridMiddle_fullPast (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u}) (hp : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle p) :
    IsExcisionGridFullPast p := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridCore] at hp
  dsimp only [IsExcisionGridFullPast]
  omega

lemma excisionGridPoint33_top (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u}) : p ≤ excisionGridPoint33 :=
  ⟨Fin.le_last _, Fin.le_last _⟩

def excisionGridFullPastCocone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion IsExcisionGridFullPast.{u})) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_nerve_joinCocone_at_bound.{u}
    (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion IsExcisionGridFullPast.{u})) excisionGridPoint33
    (fun v ↦ excisionGridPoint33_top (nerveEquiv v).val))

lemma excisionGridFullPastCocone_vertex : excisionGridFullPastCocone.{u}.vertex =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex excisionGridPoint33 :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_nerve_joinCocone_at_bound.{u}
    (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion IsExcisionGridFullPast.{u})) excisionGridPoint33
    (fun v ↦ excisionGridPoint33_top (nerveEquiv v).val))

lemma ExcisionGridExtension.full_past_cocone_colimit {X : SSet.{u}} [Quasicategory X]
    {G : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridExtension G z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone d.full excisionGridFullPastCocone) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isColimit_mapJoinCocone_of_poset_nested_canonical_bound _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridMiddle
    IsExcisionGridFullPast excisionGridMiddle_fullPast excisionGridPoint33
    (fun p _ ↦ excisionGridPoint33_top p) excisionGridFullPastCocone
    excisionGridFullPastCocone_vertex d.full d.full_colimit

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
