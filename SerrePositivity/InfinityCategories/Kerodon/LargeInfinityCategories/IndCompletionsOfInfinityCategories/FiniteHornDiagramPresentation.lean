module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FilteredPresentationShapeIso
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.FiniteCospanNerveIso

/-!
概要：元の標準 span/cospan 全図式は単一の小さい κ-filtered Yoneda 表示を持つ。
方針：有限半順序 nerve の単一表示を厳密な形状同型で往復する。
規約：元の指定全図式自身を頂点とし、全余錐の普遍性を保持する。
使われ方：I-2 c の fiber/cofiber 全族の共通添字表示。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の標準 cospan の全図式の、小さい単一 κ-filtered 表示。 -/
lemma ind_cospan_has_singleFilteredDiagramPresentation (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {C : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (horn 2 2) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSingleFilteredDiagramPresentation κ D := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSingleFilteredDiagramPresentation.precomp_iso κ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.finiteCospanNerveIso.symm _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indFinitePoset_has_singleFilteredDiagramPresentation κ
      ((SSet.uliftFunctor.{u + 1, u}).map _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.finiteCospanNerveIso.hom ≫ D))
  simpa only [Iso.symm_hom, ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp] using h

/-- 元の標準 span の全図式の、小さい単一 κ-filtered 表示。 -/
lemma ind_span_has_singleFilteredDiagramPresentation (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {C : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (horn 2 0) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSingleFilteredDiagramPresentation κ D := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSingleFilteredDiagramPresentation.precomp_iso κ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanNerveIso.symm _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indFinitePoset_has_singleFilteredDiagramPresentation κ
      ((SSet.uliftFunctor.{u + 1, u}).map _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.finiteSpanNerveIso.hom ≫ D))
  simpa only [Iso.symm_hom, ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp] using h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
