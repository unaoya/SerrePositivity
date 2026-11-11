module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.LiftedShapeCocone
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndCommaKappaCocone

/-!
概要：持ち上げた小さい試験族の全余錐の存在は、指定小図式下の coslice へ移る。
方針：元の二図式を join で貼り、同じ全余錐を元の coslice へ curry で戻す。
規約：元の試験族と指定図式を保持する。
使われ方：下方 comma の filtered 性から、指定変換を含む全余錐を構成する。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：元の小さい試験族の余錐の存在から、同じ指定図式下でも実余錐が存在する。
方針：join の全余錐を同じ coslice へ戻す。規約：全族を保持。使われ方：相対余錐。 -/
lemma nonempty_coslice_cocone_liftedShape_of_cocones
    {κ : Cardinal.{u}} [Fact κ.IsRegular] {X : SSet.{u + 1}}
    (hX : ∀ {B : SSet.{u}}, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ B →
      ∀ f : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone f))
    {A L : SSet.{u}} (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ A) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ L)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ X)
    (t : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone t) := by
  have hjoin := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_join (Fact.out : κ.IsRegular) hL hA
  let e := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso.{u, u + 1} L A
  obtain ⟨c⟩ := hX hjoin (e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry t)
  have he : e.inv ≫ (e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry t) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry t :=
    e.inv_hom_id_assoc _
  have hc : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry t)) := ⟨he ▸ c.restrict e.inv⟩
  obtain ⟨d⟩ := hc
  exact ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.diagramNestedCosliceDiagramCurry t Δ[0] d⟩
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
