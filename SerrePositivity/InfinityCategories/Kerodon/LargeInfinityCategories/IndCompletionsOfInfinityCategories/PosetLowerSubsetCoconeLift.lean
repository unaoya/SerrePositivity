module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PosetSubsetCoconeLiftStep

/-!
概要：有限半順序の任意の固定下方部分で、元の全図式 comma の指定余錐を厳密に持ち上げる。
方針：固定部分の外の極大点を除き、全体基底と余錐 pushout の段階で有限濃度帰納。
規約：元の試験族・全図式・指定余錐を保持する。
使われ方：元の表示 comma の filtered 性と下方制限の共終性。

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
/-- 概要：有限半順序の任意の下方部分への制限は指定全余錐を厳密に持ち上げる。
方針：外側の極大点除去帰納。規約：同じ全余錐。使われ方：共終性と filtered 性。 -/
lemma hasPosetSubsetCoconeLifts_of_lowerSet (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {C : SSet.{u}} [Quasicategory C] {P : Type u} [PartialOrder P] [Finite P]
    (U : Set P) (hU : IsLowerSet U) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPosetSubsetCoconeLifts κ C P U := by
  exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finitePoset_lowerSet_induction
    (fun P _ _ U ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPosetSubsetCoconeLifts κ C P U)
    (fun P _ _ U _ hfull ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPosetSubsetCoconeLifts_of_full κ U hfull)
    (fun P _ _ U _ a ha hmax ih ↦
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPosetSubsetCoconeLifts_of_point_removal κ U a ha hmax ih) P U hU

/-- 概要：元の有限半順序図式と指定下方全余錐に対する実持ち上げ。
方針：有限帰納の結論を適用。規約：元の q と G。使われ方：表示の貼り合わせ。 -/
lemma exists_diagramComma_cocone_lift_poset_lowerSet (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {P : Type u} [PartialOrder P] [Finite P] (U : Set P) (hU : IsLowerSet U)
    {C : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve P) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
    {A : SSet.{u}} (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ A)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D
      (nerveMap (OrderHom.Subtype.val U).toFunctor))) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D (nerveMap (OrderHom.Subtype.val U).toFunctor)) c = G :=
  hasPosetSubsetCoconeLifts_of_lowerSet κ U hU D A hA q G

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
