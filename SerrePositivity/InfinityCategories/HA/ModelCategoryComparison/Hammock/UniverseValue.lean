module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HammockValue

/-!
# 異なる Hom の宇宙での元の hammock の評価

概要：元の全射列の評価を同じ graph・余極限・正規化上の単体写像にする。
方針：宇宙に依存しない元の値の不変性を全単体に適用する。
規約：局所化後の実際の Hom と元の評価値を保持する。
使われ方：全 E 代数の元の高次比較と既存の π₀ 比較の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UniverseValue
open _root_.CategoryTheory
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{max u v} D]
  {W : MorphismProperty C} [W.IsMultiplicative] (L : C ⥤ D) (hL : W.IsInvertedBy L)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

lemma rowValue_eq {n : SimplexCategoryᵒᵖ} (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y).obj n)
    (k : Fin (n.unop.len + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL (τ.obj k) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL (τ.obj 0) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_eq L hL (τ.map (homOfLE (Fin.zero_le k)))).symm

def graphMap : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (L.obj X ⟶ L.obj Y) where
  app _ := ↾fun τ => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL (τ.obj 0)
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro τ
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL (τ.obj (θ.unop.toOrderHom 0)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL (τ.obj 0)
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UniverseValue.rowValue_eq L hL τ _

lemma graphMap_app {n : SimplexCategoryᵒᵖ} (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y).obj n) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UniverseValue.graphMap L hL).app n τ = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL (τ.obj 0) := rfl

lemma graphMap_wordAction {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UniverseValue.graphMap (w := b) L hL = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UniverseValue.graphMap (w := a) L hL := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro τ
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f (τ.obj 0)) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL (τ.obj 0)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction_value L hL f (τ.obj 0)

variable (X Y)

def colimitValue : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (L.obj X ⟶ L.obj Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraphDesc W X Y (fun _ => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UniverseValue.graphMap L hL)
    (fun f => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UniverseValue.graphMap_wordAction L hL f)

lemma graphInclusion_colimitValue (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UniverseValue.colimitValue L hL X Y = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UniverseValue.graphMap L hL :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_desc W X Y _ _ w

def reducedValue : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedSimplicialSet W X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (L.obj X ⟶ L.obj Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedAugmentation W X Y ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UniverseValue.colimitValue L hL X Y

lemma graphNormalization_reducedValue (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphNormalization W X Y w ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UniverseValue.reducedValue L hL X Y = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UniverseValue.graphMap L hL := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UniverseValue.reducedValue, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphNormalization_augmentation,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UniverseValue.graphInclusion_colimitValue]

lemma colimitNormalization_reducedValue :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.colimitNormalization W X Y ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UniverseValue.reducedValue L hL X Y = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UniverseValue.colimitValue L hL X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UniverseValue.reducedValue, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.colimitNormalization_augmentation, Category.id_comp]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UniverseValue
