module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardSegmentColumnFactorization
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedFixedCutCongr

/-!
# 元の区間合成の切断の前後の射列の回収

概要：元の一列と区間合成を同じ生成矢で切ったとき、接頭射と残りを厳密に回収する。
方針：元の一列を挟む因子化と指定前置射列での固定切断の一意性を使う。
規約：前後の空区間と元の端点移送を含む。
使われ方：語の圧縮で切断した prefix・残りの比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Segment
open CategoryTheory SimplicialLocalization.GeneratorWord

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} (S : Zigzag W.paths w X Y)
  (p q : Fin (w.length + 1)) (hpq : p ≤ q)
  (hd : ∀ j : Fin w.length, p.val ≤ j.val → j.val < q.val → w.direction j = .forward)
  (i : Fin w.length) (hp : p.val ≤ i.val) (hq : i.val < q.val)
  (hV : ∀ j : Fin w.length, p.val ≤ j.val → j.val < i.val → W.paths (S.arrow j))
  {a : Quiver.Total C} (P : FixedCut W a (S.arrow i))
  (Q : FixedCut W a (map .forward S p q hpq hd))

include hV in
lemma forward_cut_left : Q.left = (toColumn S p q hd i hp hq).comp P.left :=
  FixedCut.factorization_left W P (toColumn S p q hd i hp hq) (fromColumn S p q hd i hp hq)
    (toColumn_mem S p q hd i hp hq W.paths hV)
    (map_column_factorization S p q hpq hd i hp hq) Q

include hV in
lemma forward_cut_right : Q.right = P.right.comp (fromColumn S p q hd i hp hq) :=
  FixedCut.factorization_right W P (toColumn S p q hd i hp hq) (fromColumn S p q hd i hp hq)
    (toColumn_mem S p q hd i hp hq W.paths hV)
    (map_column_factorization S p q hpq hd i hp hq) Q

end SerrePositivity.EInfinity.Hammock.Segment
