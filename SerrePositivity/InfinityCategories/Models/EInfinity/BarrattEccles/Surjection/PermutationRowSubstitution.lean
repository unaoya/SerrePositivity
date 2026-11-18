module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.PermutationCompositeRow
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SubstitutionOneSlot
public import SerrePositivity.EInfinity.BarrattEccles.PermutationUnit

/-!
模型。文献の定義との比較は後で
# 合成置換の逆置換行は一出現への代入

概要：Berger–Fresse §1.5.7 の合成 table の行を既存の語の代入アルゴリズムに同定する。
方針：unary の合成から元の行の前後分割を得て、一出現の代入公式を適用する。
規約：既存 BE の逆置換の一行表示を使い、空入力も含む。
使われ方：合成 table の利用可能行の計算を元の二行から始める。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：内側 arity 1 では外側の残りラベルは変わらない（BF §1.5.7）。
方針：自然数値の挿入公式を評価する。
規約：指定値と異なるラベル。
使われ方：unary 合成の行の表示を元の行へ戻す。 -/
lemma remainingPosition_one (m : ℕ) (k : Fin (m + 1))
    (a : {a : Fin (m + 1) // a ≠ k}) : remainingPosition m 1 k a = a.val := by
  apply Fin.ext
  rw [remainingPosition_val, remainingValue]
  split_ifs <;> omega

/-- 概要：逆置換行は k の前半・k・後半に分かれる（BF §1.5.7）。
方針：unary 単位との合成の三ブロック表示を評価する。
規約：前後の文字は k を除いた部分型として保持する。
使われ方：一出現に代入する一般公式へ元の行を渡す。 -/
lemma permutation_inverse_row_split {m : ℕ} (σ : Equiv.Perm (Fin (m + 1)))
    (k : Fin (m + 1)) : List.ofFn σ.symm =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationBefore σ k).map Subtype.val ++ k :: (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationAfter σ k).map Subtype.val := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_inverse_row σ (1 : Equiv.Perm (Fin 1)) k
  rw [permutationComposition_right_unit] at h
  have hr : remainingPosition m 1 k = Subtype.val := funext (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingPosition_one m k)
  have hi : (List.ofFn (1 : Equiv.Perm (Fin 1)).symm).map (insertedPosition m 1 k) = [k] := by
    have hp : insertedPosition m 1 k 0 = k := Fin.ext (by rw [insertedPosition_val]; omega)
    simp only [List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil]
    change [insertedPosition m 1 k 0] = [k]
    rw [hp]
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationCompositeRow, hr, hi, List.singleton_append] using h

/-- 概要：実際の合成置換の逆置換行は元の逆置換行への内側行の代入（BF §1.5.7）。
方針：元の一行の分割と一出現のリスト代入を三ブロックの式へ照合する。
規約：零 arity の内側行も同じ等式で扱う。
使われ方：合成表の一段の抽出と元の二表の抽出を結ぶ。 -/
lemma permutationComposition_inverse_row_substitute {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n)) (k : Fin (m + 1)) :
    List.ofFn (permutationComposition m n k σ τ).symm =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k (List.ofFn σ.symm) [List.ofFn τ.symm] := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_inverse_row, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutation_inverse_row_split, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_one_slot]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
