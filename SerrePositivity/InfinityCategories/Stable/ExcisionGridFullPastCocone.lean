module
public import SerrePositivity.InfinityCategories.Stable.PosetNestedBoundColimit
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridExtension
public import SerrePositivity.InfinityCategories.F1B.Ind.NerveBoundCocone

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
namespace SerrePositivity.InfinityCategories
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

abbrev excisionGridPoint33 : ExcisionGridIndex.{u} := ULift.up ⟨(3, 3), by decide⟩

def IsExcisionGridFullPast (p : ExcisionGridIndex.{u}) : Prop :=
  p.down.val.1.val + p.down.val.2.val ≤ 5

abbrev ExcisionGridFullPastIndex := {p : ExcisionGridIndex.{u} // IsExcisionGridFullPast p}

lemma excisionGridMiddle_fullPast (p : ExcisionGridIndex.{u}) (hp : IsExcisionGridMiddle p) :
    IsExcisionGridFullPast p := by
  dsimp only [IsExcisionGridMiddle, IsExcisionGridCore] at hp
  dsimp only [IsExcisionGridFullPast]
  omega

lemma excisionGridPoint33_top (p : ExcisionGridIndex.{u}) : p ≤ excisionGridPoint33 :=
  ⟨Fin.le_last _, Fin.le_last _⟩

def excisionGridFullPastCocone :
    JoinCocone (nerveMap (posetSubtypeInclusion IsExcisionGridFullPast.{u})) :=
  Classical.choose (F2.Ind.exists_nerve_joinCocone_at_bound.{u}
    (nerveMap (posetSubtypeInclusion IsExcisionGridFullPast.{u})) excisionGridPoint33
    (fun v ↦ excisionGridPoint33_top (nerveEquiv v).val))

lemma excisionGridFullPastCocone_vertex : excisionGridFullPastCocone.{u}.vertex =
    nerveVertex excisionGridPoint33 :=
  Classical.choose_spec (F2.Ind.exists_nerve_joinCocone_at_bound.{u}
    (nerveMap (posetSubtypeInclusion IsExcisionGridFullPast.{u})) excisionGridPoint33
    (fun v ↦ excisionGridPoint33_top (nerveEquiv v).val))

lemma ExcisionGridExtension.full_past_cocone_colimit {X : SSet.{u}} [Quasicategory X]
    {G : nerve ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : ExcisionGridExtension G z) :
    IsColimitCone (mapJoinCocone d.full excisionGridFullPastCocone) :=
  isColimit_mapJoinCocone_of_poset_nested_canonical_bound IsExcisionGridMiddle
    IsExcisionGridFullPast excisionGridMiddle_fullPast excisionGridPoint33
    (fun p _ ↦ excisionGridPoint33_top p) excisionGridFullPastCocone
    excisionGridFullPastCocone_vertex d.full d.full_colimit

end SerrePositivity.InfinityCategories
