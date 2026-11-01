module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# 単体に先頭頂点を一つ追加する関手を構成する

## 概要
単体に先頭頂点を一つ追加する関手を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
順序写像または面・退化の標準形を明示して単体作用素を計算する。
生成作用素上の一致を、単体恒等式によって全作用素上の一致へ拡張する。

## 規約と注意
圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
表示された圏や比較射を、局所化後の同型だけで置き換えない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。
[棚卸し m0040][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0040
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Add one initial vertex to a simplex, with explicit maps
-/

@[expose] public section
open CategoryTheory

namespace SerrePositivity.SimplexPrefix

def map {n m : SimplexCategory} (f : n ⟶ m) :
    SimplexCategory.mk (n.len + 1) ⟶ SimplexCategory.mk (m.len + 1) :=
  SimplexCategory.Hom.mk ⟨Fin.cases 0 (fun i => (f.toOrderHom i).succ), by
    intro i j hij
    induction i using Fin.cases with
    | zero => exact Fin.zero_le _
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        exact Fin.succ_le_succ_iff.mpr
          (f.toOrderHom.monotone (Fin.succ_le_succ_iff.mp hij))⟩

/-- 単体に先頭頂点を一つ追加する関手を構成する。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
順序写像または面・退化の標準形を明示して単体作用素を計算する。
生成作用素上の一致を、単体恒等式によって全作用素上の一致へ拡張する。
-/
def functor : SimplexCategory ⥤ SimplexCategory where
  obj n := SimplexCategory.mk (n.len + 1)
  map := map
  map_id n := by
    ext i : 3
    induction i using Fin.cases <;> rfl
  map_comp f g := by
    ext i : 3
    induction i using Fin.cases <;> rfl

lemma map_δ {n : ℕ} (i : Fin (n + 2)) :
    functor.map (SimplexCategory.δ i) = SimplexCategory.δ i.succ := by
  ext j : 3
  induction j using Fin.cases with
  | zero =>
    change 0 = i.succ.succAbove 0
    exact (Fin.succ_succAbove_zero i).symm
  | succ j =>
    change (i.succAbove j).succ = i.succ.succAbove j.succ
    exact (Fin.succ_succAbove_succ i j).symm

lemma map_σ {n : ℕ} (i : Fin (n + 1)) :
    functor.map (SimplexCategory.σ i) = SimplexCategory.σ i.succ := by
  ext j : 3
  induction j using Fin.cases with
  | zero =>
    change 0 = i.succ.predAbove 0
    simp [Fin.predAbove]
  | succ j =>
    change (i.predAbove j).succ = i.succ.predAbove j.succ
    exact (Fin.succ_predAbove_succ i j).symm

end SerrePositivity.SimplexPrefix
