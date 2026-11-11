module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.LiftedShapeCosliceCocone
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RelativeCommaComparison

/-!
概要：元の下方余錐を厳密に持ち上げる関手では、指定変換を含む実 under comma に余錐がある。
方針：下方の coslice で全余錐を作り、その元の像を固定して持ち上げる。
規約：元の試験族と指定変換の両方を全射の等号で保持する。
使われ方：余錐図式から下方図式への制限の共終性と、旧頂点評価への伝播。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：指定像の余錐の厳密な持ち上げは、元の実 under comma の全余錐を与える。
方針：下方 coslice の全余錐を同じ射影で持ち上げる。規約：元の全族。使われ方：共終性。 -/
lemma nonempty_relativeComma_cocone_of_cocone_lifts
    {κ : Cardinal.{u}} [Fact κ.IsRegular] {X Y : SSet.{u + 1}} (F : X ⟶ Y)
    (hY : ∀ {B : SSet.{u}}, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ B →
      ∀ f : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ Y, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone f))
    (hF : ∀ {B : SSet.{u}}, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ B →
      ∀ f : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X,
      ∀ G : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ F), ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone f, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F c = G)
    {A L : SSet.{u}} (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ A) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ L)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ Y)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ X)
    (t : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z)
    (ht : q ≫ F = t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeCommaFamily F z t q ht)) := by
  obtain ⟨cT⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.nonempty_coslice_cocone_liftedShape_of_cocones hY hA hL z t
  let G : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (q ≫ F) := ⟨cT.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z, by
    rw [← Category.assoc, cT.property]
    exact ht.symm⟩
  obtain ⟨c, hc⟩ := hF hA q G
  have he : c.val ≫ F = cT.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z := congrArg Subtype.val hc
  let U := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeCommaFamily F z cT.val c.val he
  have hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ≫ U =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeCommaFamily F z t q ht := by
    apply pullback.hom_ext
    · simp only [U, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeCommaFamily, Category.assoc, pullback.lift_fst]
      exact cT.property
    · simp only [U, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeCommaFamily, Category.assoc, pullback.lift_snd]
      exact c.property
  exact ⟨⟨U, hU⟩⟩
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
