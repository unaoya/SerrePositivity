module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafElementsLeftKan
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.EquivalentCoconeRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseCoconeRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseLeftKanCanonical
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence

/-!
概要：元の全前層密度余錐の像が余極限なら、同じ全関手は元の Yoneda の左 Kan 延長。
方針：小さい元の圏への同値制限と、標準全余錐の厳密な宇宙比較を使う。
規約：指定された関手・元の全密度余錐・同じ恒等単位を保持する。
使われ方：Yoneda Hom 係数関手と指定前層宇宙変更を、同じ左 Kan 延長として比較する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafDensityLeftKan

variable {C : SSet.{u}} [Quasicategory C] {E : SSet.{u + 2}} [Quasicategory E]
  (q : (SSet.uliftFunctor.{u + 2, u + 1}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) ⟶ E)

local instance (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) v) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations.pullback_fst _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm v)))⟩

local instance (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌) :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) v) :=
  quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) v)

/-- 概要：元の全密度余錐像の余極限性は、同じ標準 Kan 全余錐像の余極限性を与える。
方針：小さい元の圏への同値制限と、標準全余錐の厳密な宇宙比較を使う。
規約：指定された関手・元の全密度余錐・同じ恒等単位を保持する。
使われ方：Yoneda Hom 係数関手と指定前層宇宙変更を、同じ左 Kan 延長として比較する。 -/
lemma presheafDensity_image_canonicalColimits
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u + 1, u + 2} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone F)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u + 1, u + 2}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)))) := by
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafElementsLeftKanComparison F
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsQCatEquivalence.ulift.{u + 1, u + 2}
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafElementsLeftKanComparison_isQCatEquivalence F)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isColimitCone_iff_restrict_equivalentShape
    ((SSet.uliftFunctor.{u + 2, u + 1}).map e) he _).mpr
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap ((SSet.uliftFunctor.{u + 2, u + 1}).map e) (𝟙 _) ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u + 1, u + 2} c).val ≫ q) = _
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ulift_restrictJoinCocone_val]
  change ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso _ 0).inv ≫
    (SSet.uliftFunctor.{u + 2, u + 1}).map (c.restrict e).val) ≫ q = _
  rw [show (c.restrict e).val = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone F).val from
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presheafElementsLeftKanComparison_coconeMap F]
  rfl

/-- 概要：同じ元の全密度余錐を保つ全関手は、持ち上げた元の Yoneda の実際の左 Kan 延長。
方針：小さい元の圏への同値制限と、標準全余錐の厳密な宇宙比較を使う。
規約：指定された関手・元の全密度余錐・同じ恒等単位を保持する。
使われ方：Yoneda Hom 係数関手と指定前層宇宙変更を、同じ左 Kan 延長として比較する。 -/
lemma presheafDensity_image_isLeftKanExtension
    (h : ∀ F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u},
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u + 1, u + 2} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone F)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) ≫ q) q
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) ≫ q)) := by
  have hcan : ∀ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u + 1, u + 2}
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) (𝟙 _) v))) := by
    intro v
    obtain ⟨F, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).surjective v
    exact presheafDensity_image_canonicalColimits q F (h F)
  have hh := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftKanExtension_refl_post_ulift_of_canonicalColimits
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C)) q hcan
  erw [(SSet.uliftFunctor.{u + 2, u + 1}).map_id] at hh
  erw [Category.id_comp] at hh
  exact hh

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafDensityLeftKan
