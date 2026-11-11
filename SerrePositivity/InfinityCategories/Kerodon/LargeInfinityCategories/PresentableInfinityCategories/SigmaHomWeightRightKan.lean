module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaUniverseCanonicalColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaHomWeightFamily
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.HomCanonicalRightKan

/-!
概要：元の大きい Hom 係数前層への全自然変換空間族は、元の Yoneda の右 Kan 延長。
方針：元の大きい前層値関手の全標準余極限性を、同じ全係数族へ適用する。
規約：元の全自然変換空間族自身と同じ元の射・恒等単位を保持する。
使われ方：同じ宇宙に持ち上げた延長の全 Hom 族との自然比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 元の全自然変換空間族自身は、同じ持ち上げた Yoneda の実際の右 Kan 延長。 -/
lemma sigmaHomWeightFamily_isRightKanExtension {C : SSet.{u}} [Quasicategory C]
    {D : SSet.{u + 1}} [Quasicategory D]
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension
      ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C))))
      ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaHomWeightFamily F₀)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaHomWeightFamily F₀)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaHomWeightFamily F₀)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homCanonical_isRightKanExtension _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaUniverseInclusion C)
    ((SSet.uliftFunctor.{u + 3, u + 2}).map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram F₀))
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaUniverseInclusion_canonicalColimits

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
