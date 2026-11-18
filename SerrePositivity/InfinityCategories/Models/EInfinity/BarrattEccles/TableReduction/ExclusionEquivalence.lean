module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Rows

/-!
模型。文献の定義との比較は後で
# 除外状態の所属の同値と抽出の一致

概要：Berger–Fresse §1.4.4 の行長移動で除外リストの加える順序を比較する。
方針：利用可能な行は除外の所属だけに依存することを再帰の各段で使う。
規約：除外リストに重複があってもよい。
使われ方：削除行を通過した後の二つの table の抽出を一致させる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable {α : Type*} [DecidableEq α]

/-- 概要：同じ値を除外する二つの状態は同じ利用可能行を与える（BF §1.4.4）。
方針：filter の各判定が同値であることを使う。
規約：除外する順序と重複数は無関係。
使われ方：行長移動で変わる除外リストを所属で比較する。 -/
lemma available_congr_removed (removed other row : List α)
    (h : ∀ a, a ∈ removed ↔ a ∈ other) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed row = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available other row := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available
  apply List.filter_congr
  intro a _
  simp only [h a]

/-- 概要：同じ値を除外する状態からの table の抽出は一致（BF §1.4.4）。
方針：各行の抽出と後続の除外状態の所属の同値を帰納する。
規約：失敗する場合も含む Option の等式。
使われ方：削除行の後で相殺候補の全後続行を同時に一致させる。 -/
lemma reduceRows_congr_removed (rows : List (List α × ℕ)) (removed other : List α)
    (h : ∀ a, a ∈ removed ↔ a ∈ other) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rows removed = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rows other := by
  induction rows generalizing removed other with
  | nil => rfl
  | cons p rows ih =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_congr_removed removed other p.1 h]
    split
    · congr 1
      apply ih
      intro a
      simp only [List.mem_append, h a]
    · rfl

/-- 概要：除外に加える一文字の順序は後続抽出を変えない（BF §1.4.4）。
方針：リストの連結の所属を論理和として比較する。
規約：元の状態・追加部分に同じ値が含まれてもよい。
使われ方：一つの値を先行行で早く除外した二つの状態を合流させる。 -/
lemma reduceRows_removed_append_singleton (rows : List (List α × ℕ))
    (removed extra : List α) (a : α) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rows (removed ++ a :: extra) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rows ((removed ++ extra) ++ [a]) := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_congr_removed
  intro x
  simp only [List.mem_append, List.mem_cons]
  tauto

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
