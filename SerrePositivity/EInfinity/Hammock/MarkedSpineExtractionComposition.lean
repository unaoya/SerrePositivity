module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineEnrichedFoldMap
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitArrowMap

/-!
# 元の hammock の抽出の単位・合成保存と生成矢の回収

概要：元の抽出は元の単位と合成を保ち、貼り戻しは同じ元の生成矢を回収する。
方針：元の各点の回収式を単体写像の等式へ移す。
規約：元の同じ抽出・貼り戻し・標準射を使う。
使われ方：豊穣自由積の普遍性を元の hammock 自身へ移す。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)

lemma extraction_unitMap (X : Paths C) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W.paths X ≫ extraction W X X =
    MarkedSpine.unitMap W X := by
  ext n p
  have hu := AllMarked.inclusion_unitPoint W X n
  exact (congrArg (markedSpine W X n X) hu).symm.trans
    (markedSpine_native W X X (AllMarked.nativeUnitPoint W X n))

lemma extraction_composition (X Y Z : Paths C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W.paths X Y Z ≫ extraction W Z X =
      (extraction W Y X ⊗ₘ extraction W Z Y) ≫ MarkedSpine.composition W X Y Z := by
  ext n p
  exact MarkedSpine.extraction_composePoint p.1 p.2

lemma generatorMap_gluing (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) :
    MarkedSpine.generatorMap W g ≫ MarkedSpine.gluing W g.val.right g.val.left =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W.paths g.val.hom.toPath := by
  ext n p
  exact MarkedSpine.glue_generatorPoint g

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
