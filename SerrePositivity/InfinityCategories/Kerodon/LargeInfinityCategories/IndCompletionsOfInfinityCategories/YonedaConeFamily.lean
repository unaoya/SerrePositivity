module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorVertexConeReindex
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramYoneda
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FiniteLimitConeFamily

/-!
概要：C の元の全錐族を、元の Ind Yoneda の全錐族へ移す。
方針：全図式 Yoneda の作用を、実錐形状の宇宙同型で前合成する。
規約：元の全族と下方図式への厳密な制限を保持する。
使われ方：有限極限錐族の filtered 補完と元の図式表示の照合。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) {A K C : SSet.{u}} [Quasicategory C]

/-- 同じ C 全錐族に対する、実錐形状を揃えた全 Ind Yoneda 族。 -/
def indYonedaConeFamily (l : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K)).obj C) :
    (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K))).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) :=
  (SSet.uliftFunctor.{u + 1, u}).map l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramYoneda κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] K) C ≫
    (pre (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso.{u, u + 1} K 0).inv).app (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)

/-- 元の全錐族の下方への制限は、同じ下方 C 全図式への Yoneda の作用そのもの。 -/
lemma indYonedaConeFamily_restriction
    (l : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K)).obj C) :
    indYonedaConeFamily κ l ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction ((SSet.uliftFunctor.{u + 1, u}).obj K) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) =
      (SSet.uliftFunctor.{u + 1, u}).map (l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K C) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramYoneda κ K C := by
  unfold indYonedaConeFamily _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction
  simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso_inv_inr]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramYoneda_restrict, ← Category.assoc, ← Functor.map_comp]

/-- 各値で読み戻した全錐は、元の C 全錐の宇宙持ち上げと Ind Yoneda の合成。 -/
lemma indYonedaConeFamily_vertex_val
    (l : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K)).obj C) (a : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone ((indYonedaConeFamily κ l).app
      (Opposite.op ⦋0⦌) (ULift.up a))).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C)
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanConeFamilyAt l a))).val := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm
    (((pre (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso.{u, u + 1} K 0).inv).app (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramYoneda κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] K) C).app _ (ULift.up (l.app _ a)))) = _
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramYoneda_vertex κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanConeFamilyAt l a).val
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanConeFamilyAt_vertex l a] at hv
  rw [hv, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexMap_precomp]
  change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso.{u, u + 1} K 0).inv ≫
    ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanConeFamilyAt l a).val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) = _
  rfl

/-- C の全極限錐族は、包含後も各値で元の全極限錐となる。 -/
lemma indYonedaConeFamily_inclusion_isLimit
    (l : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K)).obj C)
    (hl : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanConeFamilyAt l a)) (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone ((indYonedaConeFamily κ l).app
        (Opposite.op ⦋0⦌) (ULift.up a)))) := by
  let c := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone ((indYonedaConeFamily κ l).app
    (Opposite.op ⦋0⦌) (ULift.up a))
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1}
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanConeFamilyAt l a))
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C) c).val = d.val := by
    change c.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C = d.val
    rw [show c.val = _ from indYonedaConeFamily_vertex_val κ l a]
    change (_ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C = _
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_inclusion]
    rfl
  have hd := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C) c).property.symm.trans
    ((congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u + 1})
      ((SSet.uliftFunctor.{u + 1, u}).obj K) ≫ f) he).trans d.property)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_of_diagram_eq (d := d) hd he).mpr
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_isLimit _ (hl a))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
