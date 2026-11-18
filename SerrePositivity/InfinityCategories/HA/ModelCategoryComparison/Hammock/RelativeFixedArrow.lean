module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeFixedColimitMap
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeForwardSimplex

/-!
# 固定端点の hammock 余極限写像による元の射の回収

概要：元の一列の点は同じ相対関手の射像と端点移送へ送られる。
方針：元の端点の等式を消去し、既存の一列の自然性を使う。
規約：全次数の同じ元の射を保持する。
使われ方：自由 hammock 対角の元の射の左比較。
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
  (F : LocalizerMorphism W V) {X Y : C} {X' Y' : D}

lemma fixedColimitMap_arrowPoint (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
    (p : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.fixedColimitMap F hX hY).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W p n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint V (eqToHom hX.symm ≫ F.functor.map p ≫ eqToHom hY) n := by
  cases hX
  cases hY
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.fixedColimitMap, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.fixedGraphDiagramMap, eqToHom_refl,
    Category.comp_id, Category.id_comp, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap] using _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.arrowPoint_map F p n

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative
