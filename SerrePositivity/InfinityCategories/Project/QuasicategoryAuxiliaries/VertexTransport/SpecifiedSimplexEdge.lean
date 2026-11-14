module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence

/-!
概要：指定された一次単体と端点の等式による辺の構成。
方針：元の辺の面の式を一次単体の等式で輸送する。
規約：新しい辺の一次単体は入力そのものと定義上等しい。
使われ方：coherent 四面の正方形の変換で大きな定義展開を避ける。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：元の辺と等しい指定一次単体を持ち、両端を輸送した辺。
方針：一次単体を明示して二つの面の式を添える。
規約：両端の表示変更は射の向きを保つ。
使われ方：正規化した四面の辺の厳密な代表。 -/
def edgeOfSimplexWithEndpoints {X : SSet.{u}} {a b a' b' : X _⦋0⦌}
    (e : X.Edge a b) (t : X _⦋1⦌) (ht : t = e.edge)
    (ha : a = a') (hb : b = b') : X.Edge a' b' where
  edge := t
  src_eq := ((congrArg (X.δ 1) ht).trans e.src_eq).trans ha
  tgt_eq := ((congrArg (X.δ 0) ht).trans e.tgt_eq).trans hb

/-- 概要：指定一次単体による辺と両端だけを輸送した辺は同じ類。
方針：同じ両端の辺の外延性を使う。
規約：ホモトピーを新たに選択しない。
使われ方：指定関手同型の射と正規化した辺の類を照合する。 -/
lemma edgeOfSimplexWithEndpoints_homMk {X : SSet.{u}} {a b a' b' : X _⦋0⦌}
    (e : X.Edge a b) (t : X _⦋1⦌) (ht : t = e.edge)
    (ha : a = a') (hb : b = b') :
    SSet.Truncated.HomotopyCategory.homMk
        (edgeOfSimplexWithEndpoints e t ht ha hb).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (e.ofEq ha hb).toTruncated := by
  apply congrArg SSet.Truncated.HomotopyCategory.homMk
  apply SSet.Truncated.Edge.ext
  exact ht

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
