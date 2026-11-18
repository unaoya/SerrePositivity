module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Substitution

/-!
模型。文献の定義との比較は後で
# 一出現の前後の語へのリスト代入

概要：Berger–Fresse §1.5.7 の置換行への代入を前後の外側ラベルの写像に直す。
方針：指定値を除いた部分型のリストには内側部分語を消費せず通過する。
規約：内側部分語が空の場合も含む。
使われ方：逆置換行の三ブロック表示を既存 substitute と照合する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定値のない前半は外側ラベルを移すだけ（BF §1.5.7）。
方針：部分型の各値が指定値と異なることを帰納的に使う。
規約：後続語と内側部分語列は任意。
使われ方：置換行の指定値より前を代入せずに通過する。 -/
lemma substitute_remaining_prefix {m n : ℕ} (k : Fin (m + 1))
    (pre : List {a : Fin (m + 1) // a ≠ k}) (xs : List (Fin (m + 1)))
    (parts : List (List (Fin n))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (pre.map Subtype.val ++ xs) parts =
      pre.map (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k) ++ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts := by
  induction pre with
  | nil => simp only [List.map_nil, List.nil_append]
  | cons a pre ih =>
    rw [List.map_cons, List.cons_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right a.property, ih,
      List.map_cons, List.cons_append]

/-- 概要：指定値のない語は内側部分語列に依存せずラベルを移す（BF §1.5.7）。
方針：前半通過の公式を空の後続語に適用する。
規約：部分語列が残っていても消費しない。
使われ方：外側の指定値の最終除外後の行を評価する。 -/
lemma substitute_remaining_word {m n : ℕ} (k : Fin (m + 1))
    (xs : List {a : Fin (m + 1) // a ≠ k}) (parts : List (List (Fin n))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (xs.map Subtype.val) parts =
      xs.map (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k) := by
  simpa only [List.append_nil, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_remaining_prefix k xs [] parts

/-- 概要：指定値を含まない残りの語へ空の部分語列を渡すとラベル移動だけ（BF §1.5.7）。
方針：前半通過の式を空の後続語に適用する。
規約：元の語の長さは任意。
使われ方：一回の代入を終えた後半を計算する。 -/
lemma substitute_remaining_only {m n : ℕ} (k : Fin (m + 1))
    (xs : List {a : Fin (m + 1) // a ≠ k}) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute (n := n) k (xs.map Subtype.val) [] =
      xs.map (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k) := by
  simpa only [List.append_nil, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_remaining_prefix k xs [] []

/-- 概要：指定値一つの前後の語への代入は三ブロックの連結（BF §1.5.7）。
方針：前半を通過し、指定値で内側を消費し、後半も通過する。
規約：空の内側語は指定値の削除となる。
使われ方：合成置換行を実際のリスト代入として書く。 -/
lemma substitute_one_slot {m n : ℕ} (k : Fin (m + 1))
    (pre post : List {a : Fin (m + 1) // a ≠ k}) (inner : List (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (pre.map Subtype.val ++ k :: post.map Subtype.val) [inner] =
      pre.map (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k) ++
        (inner.map (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k) ++
          post.map (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_remaining_prefix, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl, List.headD_cons,
    List.tail_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_remaining_only]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
