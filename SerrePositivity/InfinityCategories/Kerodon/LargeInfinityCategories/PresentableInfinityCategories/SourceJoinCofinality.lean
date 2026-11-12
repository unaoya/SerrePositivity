module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedSimplexCategory
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.QCatEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.InitialJoinIso
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseJoinSimplexShapes
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CofinalUniverseLift

/-!
概要：弱可縮な通常圏の nerve は、始点を加えた join に right cofinal に入る。
方針：始点付加圏への包含の各 comma を、元の圏または始対象付き圏として計算する。
規約：元の join の右包含そのものを結論する。
使われ方：固定始域 coslice の filtered・pushout 余極限の終域への回収。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 始点から包含への comma の忘却は、元の通常圏との同値。 -/
private def initialStarCommaEquivalence (J : Type u) [SmallCategory J] :
    StructuredArrow (WithInitial.star : WithInitial J) WithInitial.incl ≌ J := by
  let F : StructuredArrow (WithInitial.star : WithInitial J) WithInitial.incl ⥤ J :=
    StructuredArrow.proj _ _
  have : F.Full := ⟨fun f ↦ ⟨StructuredArrow.homMk f (by subsingleton), rfl⟩⟩
  have : F.Faithful := by infer_instance
  have : F.EssSurj := ⟨fun j ↦ ⟨StructuredArrow.mk
    (default : (WithInitial.star : WithInitial J) ⟶ WithInitial.of j), ⟨Iso.refl j⟩⟩⟩
  have : F.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact F.asEquivalence

/-- 弱可縮な元の通常圏の nerve から、始点付加圏の nerve への包含は right cofinal。 -/
lemma initialInclusion_nerve_isRightCofinal (J : Type u) [SmallCategory J]
    (hJ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (nerve J)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (nerveMap (WithInitial.incl : J ⥤ WithInitial J)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.nerveMap_isRightCofinal_of_weaklyContractible_comma
  intro j
  cases j with
  | star =>
    have he := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveQCatEquivalence (initialStarCommaEquivalence J)).isQCatEquivalence
    exact he.isWeakHomotopyEquivalence.weaklyContractible_iff.mpr hJ
  | of j =>
    have ht := StructuredArrow.mkIdInitial (T := (WithInitial.incl : J ⥤ WithInitial J))
      (Y := j)
    have hpoint : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (Δ[0] : SSet.{u}) := by
      intro n b
      exact ⟨stdSimplex.isTerminalObj₀.from _, stdSimplex.isTerminalObj₀.hom_ext _ _⟩
    have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.nervePoint_isLeftCofinal ht).isWeakHomotopyEquivalence
    exact he.weaklyContractible_iff.mp hpoint.isWeaklyContractible

/-- 同じ元の join の右包含も right cofinal。 -/
lemma sourceJoinInr_nerve_isRightCofinal (J : Type u) [SmallCategory J]
    (hJ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (nerve J)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (nerve J)) := by
  have h := initialInclusion_nerve_isRightCofinal J hJ
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_initialJoinNerveMap] at h
  have hh := h.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveIso J).inv)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (nerve J) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveIso J).hom) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveIso J).inv) at hh
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh

/-- 宇宙を持ち上げた同じ小さい通常圏でも、元の右包含が right cofinal。 -/
lemma sourceJoinInr_ulift_nerve_isRightCofinal (J : Type u) [SmallCategory J]
    (hJ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (nerve J)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{max u v})
      ((SSet.uliftFunctor.{v, u}).obj (nerve J))) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift _ (sourceJoinInr_nerve_isRightCofinal J hJ)).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso.{u, v} (nerve J) 0).hom)
  rwa [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso_inr] at h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
