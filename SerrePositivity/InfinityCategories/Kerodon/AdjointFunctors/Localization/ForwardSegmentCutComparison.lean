module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardSegmentColumnFactorization
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutCongr

/-!
# 元の区間合成の切断の前後の射列の回収

概要：元の一列と区間合成を同じ生成矢で切ったとき、接頭射と残りを厳密に回収する。
方針：元の一列を挟む因子化と指定前置射列での固定切断の一意性を使う。
規約：前後の空区間と元の端点移送を含む。
使われ方：語の圧縮で切断した prefix・残りの比較。

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
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y)
  (p q : Fin (w.length + 1)) (hpq : p ≤ q)
  (hd : ∀ j : Fin w.length, p.val ≤ j.val → j.val < q.val → w.direction j = .forward)
  (i : Fin w.length) (hp : p.val ≤ i.val) (hq : i.val < q.val)
  (hV : ∀ j : Fin w.length, p.val ≤ j.val → j.val < i.val → W.paths (S.arrow j))
  {a : Quiver.Total C} (P : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W a (S.arrow i))
  (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S p q hpq hd))

include hV in
lemma forward_cut_left : Q.left = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.toColumn S p q hd i hp hq).comp P.left :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.factorization_left W P (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.toColumn S p q hd i hp hq) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fromColumn S p q hd i hp hq)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.toColumn_mem S p q hd i hp hq W.paths hV)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_column_factorization S p q hpq hd i hp hq) Q

include hV in
lemma forward_cut_right : Q.right = P.right.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fromColumn S p q hd i hp hq) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.factorization_right W P (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.toColumn S p q hd i hp hq) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fromColumn S p q hd i hp hq)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.toColumn_mem S p q hd i hp hq W.paths hV)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_column_factorization S p q hpq hd i hp hq) Q

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
