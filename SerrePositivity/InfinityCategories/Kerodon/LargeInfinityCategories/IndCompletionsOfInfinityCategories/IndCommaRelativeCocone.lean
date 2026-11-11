module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RelativeCoconeCommonExtension
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndCommaKappaCocone
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.SmallPushout
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.Pushouts
/-!
概要：元の scalar Ind comma の小さい全図式に、指定部分上の下側変換を加えた余錐を作る。
方針：単射に沿う小さい pushout で全図式を貼り、共同余錐の二つの制限を回収する。
規約：元の全族と指定変換を保持し、二余錐の射影を厳密に照合する。
使われ方：終点評価下での補間拡張の選び直し。

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
/-- 概要：指定部分上の下側変換を、同じ元の全図式の余錐と同時に延長できる。
方針：κ-small な共同図式の余錐を使う。
規約：元の射と指定値を保持。使われ方：終点評価の相対余錐。 -/
lemma exists_indComma_relative_cocones
    (κ : Cardinal.{u}) [Fact κ.IsRegular] {C A B L : SSet.{u}} [Quasicategory C]
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) _⦋0⦌) (i : A ⟶ B) [Mono i]
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ A) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ B) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ L)
    (H : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) x)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) x)
    (t : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z)
    (h : (SSet.uliftFunctor.{u + 1, u}).map i ≫ H = t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) :
    ∃ (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone H) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone t),
      d.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap ((SSet.uliftFunctor.{u + 1, u}).map i) (𝟙 (Δ[0] : SSet.{u + 1})) ≫ c.val := by
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr L A
  let e := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso.{u, u + 1} L A
  let hp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftSSet_isPushout.{u, u + 1} (IsPushout.of_hasPushout i g)
  have ht : (SSet.uliftFunctor.{u + 1, u}).map i ≫ H =
      (SSet.uliftFunctor.{u + 1, u}).map g ≫ e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry t := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso_inr, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection]
    exact h
  let F := hp.desc H (e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry t) ht
  let jB := (SSet.uliftFunctor.{u + 1, u}).map (pushout.inl i g)
  let jT := e.inv ≫ (SSet.uliftFunctor.{u + 1, u}).map (pushout.inr i g)
  have hj : (SSet.uliftFunctor.{u + 1, u}).map i ≫ jB =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr ((SSet.uliftFunctor.{u + 1, u}).obj L)
        ((SSet.uliftFunctor.{u + 1, u}).obj A) ≫ jT := by
    dsimp only [jB, jT]
    rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso_inr L A, Category.assoc, Iso.hom_inv_id_assoc,
      ← Functor.map_comp, ← Functor.map_comp, pushout.condition]
  have hFB : jB ≫ F = H := hp.inl_desc _ _ _
  have hFT : jT ≫ F = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry t := by
    dsimp only [jT]
    rw [Category.assoc, hp.inr_desc, Iso.inv_hom_id_assoc]
  have hP := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isKappaSmall_pushout_of_mono (Fact.out : κ.IsRegular) i g hB
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_join (Fact.out : κ.IsRegular) hL hA)
  obtain ⟨c₀⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.nonempty_indComma_cocone κ x hP F
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeCocones_of_commonCocone _ H z t jB jT hj F hFB hFT c₀
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
