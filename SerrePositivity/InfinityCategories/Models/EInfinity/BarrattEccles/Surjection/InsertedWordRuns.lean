module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecoveryLabels

/-!
模型。文献の定義との比較は後で
# 合成語の挿入ラベル連続区間を取り出す

概要：Berger–Fresse §1.5.9 の分割復元で、挿入部分語の終端を最初の外側ラベルから判別する。
方針：内側射影の isSome を takeWhile・dropWhile の判定に使う。
規約：外側の次の文字が指定値でなければ区間はそこで止まる。
使われ方：合成語だけから消費した分割部分語を順に復元する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：合成ラベルが内側から挿入されたかの判定（BF §1.5.9）。
方針：既存の内側射影が値を持つかで判定する。
規約：内側 arity 零でも同じ定義。
使われ方：挿入部分語の最大連続区間を切り出す。 -/
def isInserted {m n : ℕ} (k : Fin (m + 1)) (a : Fin (m + n)) : Bool :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k a).isSome

/-- 概要：元の挿入ラベルは挿入区間に属する（BF §1.5.9）。
方針：内側射影の some を評価する。
規約：全ての内側ラベル。
使われ方：挿入部分語の内部を区間として通過する。 -/
@[simp] lemma isInserted_inserted {m n : ℕ} (k : Fin (m + 1)) (a : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.isInserted k (insertedPosition m n k a) = true := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.isInserted, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_inserted, Option.isSome_some]

/-- 概要：残る外側ラベルは挿入区間に属さない（BF §1.5.9）。
方針：内側射影の none を評価する。
規約：指定値以外の外側ラベル。
使われ方：挿入区間の直後の外側文字で切断を止める。 -/
@[simp] lemma isInserted_remaining {m n : ℕ} (k : Fin (m + 1))
    (a : {a : Fin (m + 1) // a ≠ k}) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.isInserted k (remainingPosition m n k a) = false := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.isInserted, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_remaining, Option.isSome_none]

/-- 概要：外側文字で始まる後続の前の挿入区間は元の部分語そのもの（BF §1.5.9）。
方針：部分語で帰納し、外側の先頭で takeWhile が停止することを使う。
規約：空部分語・空後続も許す。
使われ方：元の分割部分語を最大連続区間として復元する。 -/
lemma takeWhile_inserted_append {m n : ℕ} (k : Fin (m + 1)) (part : List (Fin n))
    (rest : List (Fin (m + n))) (hr : ∀ a ∈ rest.head?, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.isInserted k a = false) :
    (part.map (insertedPosition m n k) ++ rest).takeWhile (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.isInserted k) =
      part.map (insertedPosition m n k) := by
  induction part with
  | nil =>
    cases rest with
    | nil => rfl
    | cons a rest =>
      have hp := hr a (by simp)
      simp only [List.map_nil, List.nil_append, List.takeWhile_cons, hp, Bool.false_eq_true,
        ite_false]
  | cons a part ih => simp [ih]

/-- 概要：最大挿入区間を省くと元の外側から始まる後続を得る（BF §1.5.9）。
方針：部分語で帰納し、外側先頭で dropWhile が停止することを使う。
規約：空部分語・空後続も許す。
使われ方：次の外側文字・次の分割部分語へ復元を進める。 -/
lemma dropWhile_inserted_append {m n : ℕ} (k : Fin (m + 1)) (part : List (Fin n))
    (rest : List (Fin (m + n))) (hr : ∀ a ∈ rest.head?, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.isInserted k a = false) :
    (part.map (insertedPosition m n k) ++ rest).dropWhile (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.isInserted k) = rest := by
  induction part with
  | nil =>
    cases rest with
    | nil => rfl
    | cons a rest =>
      have hp := hr a (by simp)
      simp only [List.map_nil, List.nil_append, List.dropWhile_cons, hp, Bool.false_eq_true,
        ite_false]
  | cons a part ih => simp [ih]

/-- 概要：指定値の直後の非退化外側語の代入は外側ラベルで始まるか空（BF §1.5.9）。
方針：次の外側文字は指定値と異なるので代入の外側分岐を使う。
規約：内側部分語列は任意。
使われ方：各分割部分語の連続区間の終端を保証する。 -/
lemma substitute_head_not_inserted {m n : ℕ} (k : Fin (m + 1))
    (xs : List (Fin (m + 1))) (parts : List (List (Fin n)))
    (hc : (k :: xs).IsChain (· ≠ ·)) :
    ∀ a ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts).head?, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.isInserted k a = false := by
  cases xs with
  | nil => simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, List.head?_nil, Option.not_mem_none, false_implies, implies_true]
  | cons b xs =>
    have hb : b ≠ k := (List.isChain_cons_cons.mp hc).1.symm
    intro a ha
    have he : remainingPosition m n k ⟨b, hb⟩ = a := by
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right hb, List.head?_cons, Option.mem_def,
        Option.some.injEq] using ha
    subst a
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.isInserted_remaining k _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
