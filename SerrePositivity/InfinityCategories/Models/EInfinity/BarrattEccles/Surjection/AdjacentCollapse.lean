module

public import Mathlib.Data.List.Chain

/-!
模型。文献の定義との比較は後で
# 合成語の逆構成で使う連続重複の縮約

概要：Berger–Fresse §1.5.9 の連続する同値だけを一つに縮める操作を構成する。
方針：右から語を読み、同じ先頭文字が続く場合だけ前のコピーを省く。
規約：離れた同値は消さない。
使われ方：合成ラベルを内外へ戻した語から元の非退化な語を復元する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse

variable {α : Type*} [DecidableEq α]

/-- 概要：連続重複を作らず先頭文字を付ける（BF §1.5.9）。
方針：後続の先頭が同じ場合だけ前のコピーを省く。
規約：空の後続には一文字を付ける。
使われ方：連続重複縮約の一段。 -/
def prepend (a : α) : List α → List α
  | [] => [a]
  | b :: xs => if a = b then b :: xs else a :: b :: xs

/-- 概要：全ての連続重複を縮めた語（BF §1.5.9）。
方針：後続を先に縮めてから先頭を付ける。
規約：離れた同値の出現順と個数は保持する。
使われ方：合成語から元の内外の語を復元する。 -/
def collapse : List α → List α
  | [] => []
  | a :: xs => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend a (collapse xs)

/-- 概要：同じ先頭文字を二回付けても一回と同じ（BF §1.5.9）。
方針：後続の先頭との一致で場合分けする。
規約：後続は縮約済みでなくてもよい。
使われ方：連続する二コピーの削除の不変性。 -/
lemma prepend_idempotent (a : α) (xs : List α) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend a (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend a xs) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend a xs := by
  cases xs with
  | nil => simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend]
  | cons b xs =>
    by_cases he : a = b <;> simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend, he]

/-- 概要：隣接する同じ二文字を一つにしても縮約語は同じ（BF §1.5.9）。
方針：二回の先頭付加の冪等性を使う。
規約：後続は任意。
使われ方：挿入部分語を指定値の一文字へ縮める。 -/
lemma collapse_duplicate (a : α) (xs : List α) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (a :: a :: xs) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (a :: xs) := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend_idempotent a (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse xs)

/-- 概要：非空な同値列の挿入は縮約後には一文字の挿入と同じ（BF §1.5.9）。
方針：反復長で帰納し、隣接する二コピーを消す。
規約：後続と同じ文字でも同じ式。
使われ方：外側への射影で挿入語が作る指定値の反復を省く。 -/
lemma collapse_replicate_append (a : α) (xs : List α) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (List.replicate (r + 1) a ++ xs) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (a :: xs) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [List.replicate_succ, List.cons_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse, ih]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend_idempotent a (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse xs)

/-- 概要：隣接非一致の語は連続重複縮約で変わらない（BF §1.5.9）。
方針：元の語で帰納し、隣接値の不一致を先頭付加の分岐へ渡す。
規約：全射性を要求しない。
使われ方：復元した縮約語を元の非退化語そのものへ戻す。 -/
lemma collapse_eq_self (xs : List α) (hc : xs.IsChain (· ≠ ·)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse xs = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse, ih hc.tail]
    cases xs with
    | nil => rfl
    | cons b xs =>
      exact ite_eq_right (List.isChain_cons_cons.mp hc).1

/-- 概要：後続の縮約結果が同じなら任意の前半を付けても同じ（BF §1.5.9）。
方針：前半の一文字付加を帰納的に戻す。
規約：前半・後半とも非退化でなくてよい。
使われ方：共有端点を持つ部分語の後続を元の語の尾部へ戻す。 -/
lemma collapse_append_congr (pre xs ys : List α) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse xs = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse ys) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (pre ++ xs) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (pre ++ ys) := by
  induction pre with
  | nil => exact h
  | cons a pre ih => exact congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend a) ih

/-- 概要：任意の位置の隣接する二コピーを消しても縮約語は同じ（BF §1.5.9）。
方針：後続の二コピーの縮約へ元の前半を戻す。
規約：全ての文字の出現順を保持する。
使われ方：分割境界の重複する端点一つを除く。 -/
lemma collapse_duplicate_in_context (pre : List α) (a : α) (post : List α) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (pre ++ a :: a :: post) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (pre ++ a :: post) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_append_congr pre _ _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_duplicate a post)

/-- 概要：一文字を重ねて切った前半・後半の連結は縮約後に元の語と同じ（BF §1.5.9）。
方針：切断点の二コピーを分離して一つを消し、take と drop を戻す。
規約：前半長は正で元の語長以下。
使われ方：重なる分割の連結を元の内側語へ戻す。 -/
lemma collapse_overlap_take (xs : List α) (r : ℕ) (hr : 0 < r) (hb : r ≤ xs.length) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (xs.take r ++ xs.drop (r - 1)) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse xs := by
  have hp : r - 1 < xs.length := by omega
  have hs : r - 1 + 1 = r := by omega
  have ht := List.take_succ_eq_append_getElem hp
  have hd := List.getElem_cons_drop hp
  rw [hs] at ht hd
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (xs.take (r - 1) ++ xs[r - 1] :: xs[r - 1] :: xs.drop r) := by
      rw [ht, ← hd, List.append_assoc, List.singleton_append]
    _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (xs.take (r - 1) ++ xs[r - 1] :: xs.drop r) :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_duplicate_in_context _ _ _
    _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse xs := by rw [hd, List.take_append_drop]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse
