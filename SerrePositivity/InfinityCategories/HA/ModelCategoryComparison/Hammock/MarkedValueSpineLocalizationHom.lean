module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MarkedValueSpineLocalizationEquivalence

/-!
# 元の通常の局所化 Hom と指定値の全因子列の同型

概要：元の Q の Hom を同じ端点の元の値の因子列へ相互に回収する。
方針：構成した両比較関手の厳密な往復を各 Hom で評価する。
規約：元の両関手の射写像を同型の順逆射として保持する。
使われ方：元の hammock 評価の弱同値を元の通常の局所化 Hom へ移す。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open _root_.CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (X Y : Paths C)

def localizationHomEquiv : (W.paths.Q.obj X ⟶ W.paths.Q.obj Y) ≃ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.ValueSpine W Y X := by
  let := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueCategory W
  exact
    { toFun p := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.localizationToValue W).map p
      invFun t := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueToLocalization W).map t
      left_inv p := by
        simpa only [Functor.comp_map, Functor.id_map, eqToHom_refl,
          Category.id_comp, Category.comp_id] using
          CategoryTheory.Functor.congr_hom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.localizationToValue_valueToLocalization W) p
      right_inv t := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueToLocalization_localizationToValue_map W t }

def valueLocalizationHomIso : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueSpace W Y X ≅
    (Functor.const SimplexCategoryᵒᵖ).obj (W.paths.Q.obj X ⟶ W.paths.Q.obj Y) :=
  (Functor.const SimplexCategoryᵒᵖ).mapIso (Equiv.toIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.localizationHomEquiv W X Y).symm)

lemma valueLocalizationHomIso_hom_app (n : SimplexCategoryᵒᵖ) (t : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.ValueSpine W Y X) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueLocalizationHomIso W X Y).hom.app n t =
      letI := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueCategory W
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueToLocalization W).map t := rfl

lemma valueLocalizationHomIso_inv_app (n : SimplexCategoryᵒᵖ)
    (p : W.paths.Q.obj X ⟶ W.paths.Q.obj Y) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueLocalizationHomIso W X Y).inv.app n p =
      letI := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.valueCategory W
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.localizationToValue W).map p := rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
