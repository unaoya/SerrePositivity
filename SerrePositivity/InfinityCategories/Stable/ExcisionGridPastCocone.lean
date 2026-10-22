module
public import SerrePositivity.InfinityCategories.Stable.PosetNestedBoundColimit
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridCorePoint
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridExtension
public import SerrePositivity.InfinityCategories.F2.Ind.NerveBoundCocone

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
namespace SerrePositivity.InfinityCategories
variable {P : Type u} [PartialOrder P]

def IsExcisionGridPast (p : ExcisionGridCoreIndex.{u}) : Prop :=
  p.val.val.down.val.1.val + p.val.val.down.val.2.val ≤ 3

abbrev ExcisionGridPastIndex := {p : ExcisionGridCoreIndex.{u} // IsExcisionGridPast p}

lemma excisionGridSeed_past (p : ExcisionGridCoreIndex.{u}) (hp : IsExcisionGridSeed p) :
    IsExcisionGridPast p := by
  exact hp.trans (by decide)

lemma excisionGridCorePoint_top (p : ExcisionGridCoreIndex.{u}) :
    p ≤ excisionGridCorePoint 2 2 := p.property

def excisionGridPastCocone :
    JoinCocone (nerveMap (posetSubtypeInclusion IsExcisionGridPast.{u})) :=
  Classical.choose (F2.Ind.exists_nerve_joinCocone_at_bound.{u}
    (nerveMap (posetSubtypeInclusion IsExcisionGridPast.{u})) (excisionGridCorePoint 2 2)
    (fun v ↦ excisionGridCorePoint_top (nerveEquiv v).val))

lemma excisionGridPastCocone_vertex : excisionGridPastCocone.{u}.vertex =
    nerveVertex (excisionGridCorePoint 2 2) :=
  Classical.choose_spec (F2.Ind.exists_nerve_joinCocone_at_bound.{u}
    (nerveMap (posetSubtypeInclusion IsExcisionGridPast.{u})) (excisionGridCorePoint 2 2)
    (fun v ↦ excisionGridCorePoint_top (nerveEquiv v).val))

lemma ExcisionGridExtension.past_cocone_colimit {X : SSet.{u}} [Quasicategory X]
    {G : nerve ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : ExcisionGridExtension G z) :
    IsColimitCone (mapJoinCocone d.core excisionGridPastCocone) :=
  isColimit_mapJoinCocone_of_poset_nested_canonical_bound IsExcisionGridSeed
    IsExcisionGridPast excisionGridSeed_past (excisionGridCorePoint 2 2)
    (fun p _ ↦ excisionGridCorePoint_top p) excisionGridPastCocone
    excisionGridPastCocone_vertex d.core d.core_colimit

end SerrePositivity.InfinityCategories
