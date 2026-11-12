module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag

/-!
# backward 一列の縦射の恒等と合成

概要：元の二つの端点成分の恒等・合成が一列の縦比較にも一致する。
方針：二つの頂点で直接検証する。
規約：接合点の等式の移送を局所化後の等式に弱めない。
使われ方：元の全体の zigzag の図式の関手性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {X Y X' Y' X'' Y'' : C}

lemma movingHom_id {e : Y ⟶ X} (he : W e) (hx : W (𝟙 X)) (hy : W (𝟙 Y))
    (h : e ≫ 𝟙 X = 𝟙 Y ≫ e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.movingHom he he (𝟙 X) (𝟙 Y) hx hy h = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj e he) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
  intro i
  change Fin 2 at i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

lemma movingHom_comp {e : Y ⟶ X} {e' : Y' ⟶ X'} {e'' : Y'' ⟶ X''}
    (he : W e) (he' : W e') (he'' : W e'')
    (x : X ⟶ X') (y : Y ⟶ Y') (x' : X' ⟶ X'') (y' : Y' ⟶ Y'')
    (hx : W x) (hy : W y) (hx' : W x') (hy' : W y')
    (h : e ≫ x = y ≫ e') (h' : e' ≫ x' = y' ≫ e'')
    (hh : e ≫ (x ≫ x') = (y ≫ y') ≫ e'') :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.movingHom he he' x y hx hy h).comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.movingHom he' he'' x' y' hx' hy' h') =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.movingHom he he'' (x ≫ x') (y ≫ y') (W.comp_mem _ _ hx hx')
        (W.comp_mem _ _ hy hy') hh := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
  intro i
  change Fin 2 at i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

@[reassoc] lemma movingHom_app_comp {e : Y ⟶ X} {e' : Y' ⟶ X'} {e'' : Y'' ⟶ X''}
    (he : W e) (he' : W e') (he'' : W e'')
    (x : X ⟶ X') (y : Y ⟶ Y') (x' : X' ⟶ X'') (y' : Y' ⟶ Y'')
    (hx : W x) (hy : W y) (hx' : W x') (hy' : W y')
    (h : e ≫ x = y ≫ e') (h' : e' ≫ x' = y' ≫ e'') (i : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.movingHom he he' x y hx hy h).app i ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.movingHom he' he'' x' y' hx' hy' h').app i =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.movingHom he he'' (x ≫ x') (y ≫ y') (W.comp_mem _ _ hx hx')
        (W.comp_mem _ _ hy hy') (by
          rw [← Category.assoc, h, Category.assoc, h', ← Category.assoc])).app i := by
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
