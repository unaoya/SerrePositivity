module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeFixedColimitMap
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeForwardSimplex

/-!
# 固定端点を保つ元の相対 hammock 写像の単位保存

概要：端点の等式移送後も元の空語の単位点を回収する。
方針：元の相対写像の単位の式へ同じ端点等式を代入する。
規約：元の各次数の実単位を保持する。
使われ方：自由 hammock 対角の豊穣単位。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative
open _root_.CategoryTheory
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) {X : C} {Y : D}

lemma fixedColimitMap_unit_point (h : F.functor.obj X = Y) (n : SimplexCategoryᵒᵖ) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.fixedColimitMap F h h).app n ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W X).app n PUnit.unit) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit V Y).app n PUnit.unit := by
  cases h
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.fixedColimitMap, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.fixedGraphDiagramMap, eqToHom_refl,
    Category.comp_id, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap] using _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitUnit_point F X n

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative
