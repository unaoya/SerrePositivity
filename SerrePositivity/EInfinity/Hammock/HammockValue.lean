module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagValueGraph
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagWordValue
public import SerrePositivity.EInfinity.Hammock.ReducedColimit

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
namespace SerrePositivity.EInfinity.Hammock.Zigzag.Value
open CategoryTheory

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {W : MorphismProperty C} [W.IsMultiplicative] (L : C ⥤ D) (hL : W.IsInvertedBy L)
  (X Y : C)

lemma graphMap_wordAction {a b : Word} (f : a ⟶ b) :
    (graphDiagram W X Y).map f ≫ graphMap (w := b) L hL = graphMap (w := a) L hL := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro τ
  change value L hL (WordAction.obj f (τ.obj 0)) = value L hL (τ.obj 0)
  exact wordAction_value L hL f (τ.obj 0)

def colimitValue : colimitGraph W X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (L.obj X ⟶ L.obj Y) :=
  colimitGraphDesc W X Y (fun _ => graphMap L hL)
    (fun f => graphMap_wordAction L hL X Y f)

lemma graphInclusion_colimitValue (w : Word) :
    graphInclusion W X Y w ≫ colimitValue L hL X Y = graphMap L hL :=
  graphInclusion_desc W X Y _ _ w

def reducedValue : reducedSimplicialSet W X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (L.obj X ⟶ L.obj Y) :=
  reducedAugmentation W X Y ≫ colimitValue L hL X Y

lemma graphNormalization_reducedValue (w : Word) :
    graphNormalization W X Y w ≫ reducedValue L hL X Y = graphMap L hL := by
  rw [reducedValue, ← Category.assoc, graphNormalization_augmentation,
    graphInclusion_colimitValue]

lemma colimitNormalization_reducedValue :
    colimitNormalization W X Y ≫ reducedValue L hL X Y = colimitValue L hL X Y := by
  rw [reducedValue, ← Category.assoc, colimitNormalization_augmentation, Category.id_comp]

end SerrePositivity.EInfinity.Hammock.Zigzag.Value
