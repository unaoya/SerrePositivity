module

public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafDensityLeftKan
public import SerrePositivity.InfinityCategories.F2.Presentable.YonedaHomWeightColimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseYonedaComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.FullyFaithfulJointHom
public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftKanRestrictionIso
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensity
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityFullyFaithful

/-!
概要：Yoneda Hom 全係数関手と前層の指定宇宙変更は、同じ元の Yoneda の左 Kan 延長。
方針：両関手の小 coherent 余極限保存を、元の全前層密度余錐に適用する。
規約：全関手・同じ元の Yoneda・元の恒等単位を保持する。
使われ方：両変数で自然な全前層 Yoneda 評価比較への普遍性入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open F2.Ind
variable (C : SSet.{u}) [Quasicategory C]

/-- 概要：指定された前層の宇宙変更自身は、持ち上げた元の Yoneda の左 Kan 延長。
方針：両関手の小 coherent 余極限保存を、元の全前層密度余錐に適用する。
規約：全関手・同じ元の Yoneda・元の恒等単位を保持する。
使われ方：両変数で自然な全前層 Yoneda 評価比較への普遍性入力。 -/
lemma presheafUniverseDiagram_isLeftKanExtension :
    IsLeftKanExtension ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap C))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap C) ≫
        presheafUniverseDiagram C) (presheafUniverseDiagram C)
      (functorHomotopyRefl ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap C) ≫
        presheafUniverseDiagram C)) :=
  presheafDensity_image_isLeftKanExtension _ (fun F =>
    presheafUniverseDiagram_map_isColimit _ _ (presheafDensityCocone_isColimit F))

/-- 概要：元の全 Yoneda Hom 係数関手自身は、持ち上げた元の Yoneda の左 Kan 延長。
方針：両関手の小 coherent 余極限保存を、元の全前層密度余錐に適用する。
規約：全関手・同じ元の Yoneda・元の恒等単位を保持する。
使われ方：両変数で自然な全前層 Yoneda 評価比較への普遍性入力。 -/
lemma yonedaHomWeightDiagram_isLeftKanExtension :
    IsLeftKanExtension ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap C))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap C) ≫
        presheafHomWeightDiagram (yonedaInfinityMap C))
      (presheafHomWeightDiagram (yonedaInfinityMap C))
      (functorHomotopyRefl ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap C) ≫
        presheafHomWeightDiagram (yonedaInfinityMap C))) :=
  presheafDensity_image_isLeftKanExtension _ (fun F =>
    yonedaHomWeightDiagram_map_isColimit _ _ (presheafDensityCocone_isColimit F))

/-- 概要：両左 Kan 候補の元の Yoneda 制限は、全 C 変数で自然同型。
方針：両関手の小 coherent 余極限保存を、元の全前層密度余錐に適用する。
規約：全関手・同じ元の Yoneda・元の恒等単位を保持する。
使われ方：両変数で自然な全前層 Yoneda 評価比較への普遍性入力。 -/
def yonedaWeightLeftKan_restrictionIso :
    FunctorIso
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap C) ≫
        presheafHomWeightDiagram (yonedaInfinityMap C))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap C) ≫
        presheafUniverseDiagram C) :=
  (yonedaInfinityMap_fullyFaithfulRestrictionIso (yonedaInfinityMap C)
    (yonedaInfinityMap_isFullyFaithful C)).symm ≪≫ (yonedaInfinityMap_universeIso C).symm

/-- 概要：元の全 Yoneda Hom 係数関手と、同じ前層宇宙変更の全関手自然同型。
方針：両関手の小 coherent 余極限保存を、元の全前層密度余錐に適用する。
規約：全関手・同じ元の Yoneda・元の恒等単位を保持する。
使われ方：両変数で自然な全前層 Yoneda 評価比較への普遍性入力。 -/
def yonedaHomWeightDiagram_universeIso :
    FunctorIso (presheafHomWeightDiagram (yonedaInfinityMap C)) (presheafUniverseDiagram C) :=
  leftKanReflRestrictionIso
    ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap C))
    (yonedaHomWeightDiagram_isLeftKanExtension C)
    (presheafUniverseDiagram_isLeftKanExtension C) (yonedaWeightLeftKan_restrictionIso C)

end SerrePositivity.InfinityCategories.HomotopyLimits
