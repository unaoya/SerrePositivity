module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HammockValue
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueRelative
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeColimitMap

/-!
# 元の全語の評価と相対関手の合成

概要：元の相対関手で送った hammock の評価は合成関手による同じ評価に一致する。
方針：元の全語の標準射上で既存の zigzag 評価の合成則を使う。
規約：結論は元の colimitMap と元の colimitValue の等式。
使われ方：指定部分圏の評価自身の弱同値性への移送。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value
open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) (L : D ⥤ E) (hL : V.IsInvertedBy L) (X Y : C)

lemma colimitValue_relative :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap F X Y ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.colimitValue L hL (F.functor.obj X) (F.functor.obj Y) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.colimitValue (F.functor ⋙ L) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.relativeInverts F L hL) X Y := by
  apply colimit.hom_ext
  intro w
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap F X Y ≫ _ =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w ≫ _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.graphInclusion_colimitMap, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.graphInclusion_colimitValue, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.graphInclusion_colimitValue]
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro τ
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_relative F L hL (τ.obj 0)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value
