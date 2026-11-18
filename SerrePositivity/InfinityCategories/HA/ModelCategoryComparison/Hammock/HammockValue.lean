module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueGraph
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagWordValue
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ReducedColimit

/-!
# 元の全語の hammock から定数 Hom への評価

概要：元の全語の余極限と元の reduced hammock を、同じ反転関手の Hom へ評価する。
方針：元の固定語の評価と全語の作用への不変性を、元の余極限の普遍性へ渡す。
規約：元の標準射・正規化・augmentation への回収式を保持する。
使われ方：自由解像の各次数の通常の局所化 Hom への右比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value
open _root_.CategoryTheory

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {W : MorphismProperty C} [W.IsMultiplicative] (L : C ⥤ D) (hL : W.IsInvertedBy L)
  (X Y : C)

lemma graphMap_wordAction {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueGraph.graphMap (w := b) L hL = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueGraph.graphMap (w := a) L hL := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro τ
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f (τ.obj 0)) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL (τ.obj 0)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction_value L hL f (τ.obj 0)

def colimitValue : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (L.obj X ⟶ L.obj Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraphDesc W X Y (fun _ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueGraph.graphMap L hL)
    (fun f => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.graphMap_wordAction L hL X Y f)

lemma graphInclusion_colimitValue (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.colimitValue L hL X Y = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueGraph.graphMap L hL :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_desc W X Y _ _ w

def reducedValue : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedSimplicialSet W X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (L.obj X ⟶ L.obj Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedAugmentation W X Y ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.colimitValue L hL X Y

lemma graphNormalization_reducedValue (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphNormalization W X Y w ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.reducedValue L hL X Y = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueGraph.graphMap L hL := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.reducedValue, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphNormalization_augmentation,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.graphInclusion_colimitValue]

lemma colimitNormalization_reducedValue :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.colimitNormalization W X Y ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.reducedValue L hL X Y = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.colimitValue L hL X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.reducedValue, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.colimitNormalization_augmentation, Category.id_comp]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value
