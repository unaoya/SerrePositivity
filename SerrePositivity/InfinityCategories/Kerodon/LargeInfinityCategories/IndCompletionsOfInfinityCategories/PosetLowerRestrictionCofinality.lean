module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FinitePosetDiagramFiltered
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CofinalityOfCoconeLifts

/-!
概要：元の有限半順序図式の任意の下方部分への表示 comma 制限は right cofinal。
方針：下方部分の filtered 性と、元の指定像余錐の厳密持ち上げを使う。
規約：元の全制限写像そのものを扱う。
使われ方：各指定点の弱下方部分を経由する評価の共終性。

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
/-- 概要：元の有限半順序の下方部分への表示制限自身は right cofinal。
方針：指定全余錐持ち上げの共終性判定。
規約：同じ元の制限。使われ方：各点密度の回収。 -/
lemma diagramCommaRestriction_poset_lowerSet_isRightCofinal (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {P : Type u} [PartialOrder P] [Finite P] (U : Set P) (hU : IsLowerSet U)
    {C : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve P) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaRestriction κ D (nerveMap (OrderHom.Subtype.val U).toFunctor)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_of_cocone_lifts (κ := κ) _ ?_ ?_
  · intro A hA q
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.nonempty_finitePosetDiagramComma_cocone κ _ hA q
  · intro A hA q G
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_diagramComma_cocone_lift_poset_lowerSet κ U hU D hA q G

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
