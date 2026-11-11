module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardPathSegmentMarked
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnRecovery

/-!
# 元の語の圧縮に沿う各列の非指定性の判定

概要：圧縮後の列の非指定文字列が空である条件を元の同じ fiber の全列で判定する。
方針：forward 区間の指定性の完全な判定と backward 列の指定性を使う。
規約：空 fiber の恒等列も含む。
使われ方：最初の非指定列の元の位置と圧縮後の位置の照合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths a X Y)

lemma column_wordAction_eq_nil_iff (j : Fin b.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) j = [] ↔
      ∀ i : Fin a.length, f.orderHom i = j → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W S i = [] := by
  cases hj : b.direction j with
  | forward =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_eq_nil_iff]
    have he := eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_obj_heq f S .forward j hj)
    have ht : W.paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) j hj) ↔
        W.paths ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S).arrow j) := by
      change W.paths (eqToHom _ ≫ _ ≫ eqToHom _) ↔ _
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem _ _ _
    rw [← ht, he, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forward_path_map_mem_iff]
    constructor
    · intro h i hi
      have hb := (f.fiber_iff j i).2 hi
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_eq_nil_iff W (S.arrow i)).2 (h i hb.1 hb.2)
    · intro h i hi hi'
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_eq_nil_iff W (S.arrow i)).1
        (h i ((f.fiber_iff j i).1 ⟨hi, hi'⟩))
  | backward =>
    constructor
    · intro _ i hi
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column_backward W S i
        ((f.direction_eq i).symm.trans ((congrArg b.direction hi).trans hj))
    · intro _
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column_backward W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) j hj

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
