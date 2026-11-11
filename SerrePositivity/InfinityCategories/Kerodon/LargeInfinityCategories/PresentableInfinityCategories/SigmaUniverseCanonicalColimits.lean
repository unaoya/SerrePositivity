module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaUniverseDensity
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseCoconeRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseLeftKanCanonical
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaSiftedContinuousLeftKan
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence

/-!
概要：元の P_Σ の大きい前層値関手自身は、持ち上げた元の Yoneda の左 Kan 延長。
方針：同じ標準全余錐を小さい密度形状へ制限し、指定宇宙変更の保存性へ戻す。
規約：元の添字・同じ全余錐の射と元の恒等単位を保持する。
使われ方：自然変換空間の全族の実際の右 Kan 条件。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {C : SSet.{u}} [Quasicategory C]

/-- 元の標準 Kan 余錐の包含像の持ち上げは、同じ前層宇宙変更で余極限となる。 -/
lemma sigmaUniverseCanonical_image_isColimit (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram C)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u + 1, u + 2}
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C) v))) := by
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C) v
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaElementsLeftKanComparison v
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsQCatEquivalence.ulift.{u + 1, u + 2}
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaElementsLeftKanComparison_isQCatEquivalence v)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isColimitCone_iff_restrict_equivalentShape
    ((SSet.uliftFunctor.{u + 2, u + 1}).map e) he _).mpr
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaUniverseInclusion_density_isColimit v
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaUniverseInclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.mapJoinCocone_universe_comp] at hd
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr hd
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap ((SSet.uliftFunctor.{u + 2, u + 1}).map e) (𝟙 _) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u + 1, u + 2} c).val ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram C) = _
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ulift_restrictJoinCocone_val]
  change ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso _ 0).inv ≫
      (SSet.uliftFunctor.{u + 2, u + 1}).map (c.restrict e).val) ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram C = _
  rw [show (c.restrict e).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaVertexDensityCocone v)).val from
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaLeftKanCanonicalCocone_restrict_val (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C) v]
  rfl

/-- 元の大きい前層値関手の同じ標準 Kan 全余錐は、実際に余極限。 -/
lemma sigmaUniverseInclusion_canonicalColimits :
    ∀ v : ((SSet.uliftFunctor.{u + 2, u + 1}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C)) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaUniverseInclusion C) v) := by
  rintro ⟨v⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftKanCanonicalCocone_post_ulift_isColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinityInclusion C) v (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram C)
    (sigmaUniverseCanonical_image_isColimit v)

/-- 元の大きい前層値関手自身は、持ち上げた元の Yoneda の実際の左 Kan 延長。 -/
lemma sigmaUniverseInclusion_isLeftKanExtension :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaUniverseInclusion C) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaUniverseInclusion C)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaUniverseInclusion C)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanExtension_refl_of_canonicalColimits _ _ sigmaUniverseInclusion_canonicalColimits

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
