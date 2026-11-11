module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafDensityLeftKan
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.YonedaHomWeightColimits
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseYonedaComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.FullyFaithfulJointHom
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.LeftKanRestrictionIso
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.PresheafDensity
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaInfinityFullyFaithful

/-!
概要：Yoneda Hom 全係数関手と前層の指定宇宙変更は、同じ元の Yoneda の左 Kan 延長。
方針：両関手の小 coherent 余極限保存を、元の全前層密度余錐に適用する。
規約：全関手・同じ元の Yoneda・元の恒等単位を保持する。
使われ方：両変数で自然な全前層 Yoneda 評価比較への普遍性入力。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable (C : SSet.{u}) [Quasicategory C]

/-- 概要：指定された前層の宇宙変更自身は、持ち上げた元の Yoneda の左 Kan 延長。
方針：両関手の小 coherent 余極限保存を、元の全前層密度余錐に適用する。
規約：全関手・同じ元の Yoneda・元の恒等単位を保持する。
使われ方：両変数で自然な全前層 Yoneda 評価比較への普遍性入力。 -/
lemma presheafUniverseDiagram_isLeftKanExtension :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram C) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram C)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram C)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafDensityLeftKan.presheafDensity_image_isLeftKanExtension _ (fun F =>
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram_map_isColimit _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafDensityCocone_isColimit F))

/-- 概要：元の全 Yoneda Hom 係数関手自身は、持ち上げた元の Yoneda の左 Kan 延長。
方針：両関手の小 coherent 余極限保存を、元の全前層密度余錐に適用する。
規約：全関手・同じ元の Yoneda・元の恒等単位を保持する。
使われ方：両変数で自然な全前層 Yoneda 評価比較への普遍性入力。 -/
lemma yonedaHomWeightDiagram_isLeftKanExtension :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C))
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C))
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafDensityLeftKan.presheafDensity_image_isLeftKanExtension _ (fun F =>
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.yonedaHomWeightDiagram_map_isColimit _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafDensityCocone_isColimit F))

/-- 概要：両左 Kan 候補の元の Yoneda 制限は、全 C 変数で自然同型。
方針：両関手の小 coherent 余極限保存を、元の全前層密度余錐に適用する。
規約：全関手・同じ元の Yoneda・元の恒等単位を保持する。
使われ方：両変数で自然な全前層 Yoneda 評価比較への普遍性入力。 -/
def yonedaWeightLeftKan_restrictionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C) ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram C) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.FullyFaithfulJointHom.yonedaInfinityMap_fullyFaithfulRestrictionIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap_isFullyFaithful C)).symm ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.yonedaInfinityMap_universeIso C).symm

/-- 概要：元の全 Yoneda Hom 係数関手と、同じ前層宇宙変更の全関手自然同型。
方針：両関手の小 coherent 余極限保存を、元の全前層密度余錐に適用する。
規約：全関手・同じ元の Yoneda・元の恒等単位を保持する。
使われ方：両変数で自然な全前層 Yoneda 評価比較への普遍性入力。 -/
def yonedaHomWeightDiagram_universeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C)) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafUniverseDiagram C) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftKanReflRestrictionIso
    ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap C))
    (yonedaHomWeightDiagram_isLeftKanExtension C)
    (presheafUniverseDiagram_isLeftKanExtension C) (yonedaWeightLeftKan_restrictionIso C)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
