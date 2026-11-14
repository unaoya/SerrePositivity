module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.UniverseRightKanCanonical
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.KanOppositeCanonicalLimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaLeftKanHomCanonical
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.PresheafHomWeights

/-!
概要：元の P_Σ 左 Kan 延長の全共同 Hom 族は、持ち上げた元の Yoneda の右 Kan 延長。
方針：元の標準全余錐を反転し、同じ全 Hom 錐と局所添字の宇宙同型を使う。
規約：全係数を持つ元の共同 Hom 関手と、元の反転した Yoneda 自身を保持する。
使われ方：延長の全自然 Hom 表示を、右 Kan 延長の全自然比較へ接続する。

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

/-- 元の延長の全共同 Hom 族自身は、持ち上げた元の Yoneda の実際の右 Kan 延長。 -/
lemma sigmaLeftKanHom_isRightKanExtension {C : SSet.{u}} [Quasicategory C]
    {D : SSet.{u + 1}} [Quasicategory D]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D}
    {G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C ⟶ D}
    (β : SSet.Homotopy F₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C ≫ G))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) F₀ G β) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C)))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C)) ≫
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map G) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap D))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map G) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap D)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C)) ≫
          ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map G) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap D))) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.rightKanExtension_refl_post_ulift_of_canonicalLimits
  intro c
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.rightKanCanonicalCone_op_isLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) G
    (SSet.opObjEquiv c) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaLeftKanExtension_canonicalColimits β hβ (SSet.opObjEquiv c))
  have he : SSet.opObjEquiv.symm (SSet.opObjEquiv c) = c := Equiv.symm_apply_apply _ c
  rw [he] at h
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coyonedaInfinityMap_map_isLimit _ h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
