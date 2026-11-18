module

public import SerrePositivity.EInfinity.BarrattEccles.PermutationCompositionValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapSegments

/-!
模型。文献の定義との比較は後で
# 全射語の出現順のリスト代入

概要：Berger–Fresse §1.2.4 の指定値の各出現へ内側の部分語を順に代入する。
方針：指定値では部分語列を一つ消費し、他の値には既存の BE の残りラベルを使う。
規約：外側 arity は m+1、内側は n、出力は m+n。空部分語も許す。
使われ方：端点を重ねた分割の各合成語を構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定値の全出現へ部分語を順に代入する（BF §1.2.4）。
方針：指定値に出会うと部分語を消費し、その値を挿入区間へ移す。
規約：部分語不足は空部分語で補うが、合成では個数一致を証明して使う。
使われ方：各分割添字に対応する実際の合成リスト。 -/
def substitute {m n : ℕ} (k : Fin (m + 1)) :
    List (Fin (m + 1)) → List (List (Fin n)) → List (Fin (m + n))
  | [], _ => []
  | a :: xs, parts =>
    if h : a = k then
      (parts.headD []).map (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k) ++
        substitute k xs parts.tail
    else
      _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k ⟨a, h⟩ :: substitute k xs parts

/-- 概要：代入語の長さは元の語の指定値を各部分語の長さで置き換えたもの（BF §1.2.4）。
方針：外側語で帰納し、指定値のときだけ部分語を一つ消費する。
規約：部分語数は指定値の出現回数に一致する。
使われ方：部分合成の語の長さと次数の和を検証する。 -/
lemma substitute_length {m n : ℕ} (k : Fin (m + 1))
    (xs : List (Fin (m + 1))) (parts : List (List (Fin n)))
    (h : parts.length = xs.count k) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts).length + xs.count k = xs.length + parts.flatten.length := by
  induction xs generalizing parts with
  | nil => simp only [List.count_nil] at h; simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, List.length_eq_zero_iff.mp h]
  | cons a xs ih =>
    by_cases ha : a = k
    · subst a
      cases parts with
      | nil => simp at h
      | cons part parts =>
        have ht : parts.length = xs.count k := by simpa using h
        have hi := ih parts ht
        simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl, List.headD_cons, List.tail_cons,
          List.length_append, List.length_map, List.count_cons_self, List.length_cons,
          List.flatten_cons] at *
        omega
    · have ht : parts.length = xs.count k := by simpa [ha] using h
      have hi := ih parts ht
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right ha, List.length_cons]
      have hc : (a :: xs).count k = xs.count k := by simp [ha]
      rw [hc]
      omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
