module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordActionCutComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstGeneratorImage

/-!
# 元の最小非指定列の像の切断の接頭射と残り

概要：最初の非指定列を含む fiber の前後の射列から圧縮後の切断を回収する。
方針：最小性による前置区間の指定性を元の固定切断の比較に代入する。
規約：元の端点移送・同じ生成矢・全射列を保持する。
使われ方：prefix・残りの元の全語の余極限での像の一致。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstFiberCuts
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths a X Y)
  (h : ∃ i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W S i ≠ [])

lemma image_forward : b.direction (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h)) = .forward :=
  (f.direction_eq _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W S h)

def prefixMap := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordActionCutComparison.prefixMap W f S (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h) rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstFiberCuts.image_forward W f S h)

def residualMap := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordActionCutComparison.residual W f S (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h) rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstFiberCuts.image_forward W f S h)

lemma prefixMap_mem : W.paths (prefixMap W f S h) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordActionCutComparison.prefix_mem W f S (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h)
    rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstFiberCuts.image_forward W f S h) (fun k _ hk => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.before_firstColumn_mem W S h k hk)

variable {g : Quiver.Total C} (P : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W g (S.arrow (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h)))
  (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W g ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S).arrow (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h))))

lemma cut_left : HEq Q.left ((prefixMap W f S h).comp P.left) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordActionCutComparison.cut_left W f S (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h)
    rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstFiberCuts.image_forward W f S h) (fun k _ hk => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.before_firstColumn_mem W S h k hk) P Q

lemma cut_right : HEq Q.right (P.right.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstFiberCuts.residualMap W f S h)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordActionCutComparison.cut_right W f S (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S h)
    rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstFiberCuts.image_forward W f S h) (fun k _ hk => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.before_firstColumn_mem W S h k hk) P Q

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstFiberCuts
