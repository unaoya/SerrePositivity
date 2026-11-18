module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionBoundaryCases
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.PermutationRowSubstitution
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SubstitutionLabels

/-!
模型。文献の定義との比較は後で
# 空語挿入の指定値削除

概要：Berger–Fresse §1.2.4・§1.5.7 の nullary 合成を指定値の削除として記述する。
方針：空集合の文字列を消去し、残る文字を既存の BE のラベル写像で詰める。
規約：出力 arity 零も含み、削除後の退化語は listGenerator が零にする。
使われ方：空語の χ 合成と実際の BE 逆置換行を同じ削除操作へ比較する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定値は消し、他の文字を詰める部分ラベル写像（BF §1.2.4）。
方針：指定値以外に BE の remainingPosition を適用する。
規約：出力は Fin (m+0)。
使われ方：空語挿入を filterMap で記述する。 -/
def eraseSlotLabel {m : ℕ} (k a : Fin (m + 1)) : Option (Fin (m + 0)) :=
  if h : a = k then none else some (_root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m 0 k ⟨a, h⟩)

/-- 概要：指定値を全て消去して残る文字を詰める（BF §1.2.4）。
方針：各文字の部分ラベル写像を filterMap する。
規約：出現が複数でも定義し、合成の有限和は別途その場合を零にする。
使われ方：χ と BE の nullary 合成の共通の語。 -/
def eraseSlotWord {m : ℕ} (k : Fin (m + 1)) (xs : List (Fin (m + 1))) :
    List (Fin (m + 0)) := xs.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel k)

/-- 概要：削除されない二文字は出力ラベルで区別される（BF §1.5.7）。
方針：some となる場合を取り出し、remainingPosition の単射性を使う。
規約：指定値における none は単射性の対象外。
使われ方：除外リストと可用行を同じ削除操作で射影する。 -/
lemma eraseSlotLabel_partial_injective {m : ℕ} (k : Fin (m + 1))
    (a a' : Fin (m + 1)) (b : Fin (m + 0))
    (ha : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel k a = some b) (ha' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel k a' = some b) : a = a' := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel at ha ha'
  split at ha
  · contradiction
  · split at ha'
    · contradiction
    · exact congrArg Subtype.val
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingPosition_injective m 0 k ((Option.some.inj ha).trans (Option.some.inj ha').symm))

/-- 概要：削除語の長さと指定値の出現数の和は元の語長（BF §1.2.4）。
方針：各文字で指定値か否かを分けて帰納する。
規約：空語・複数出現を含む。
使われ方：一出現の空語挿入が外側次数を保つことを確認する。 -/
lemma eraseSlotWord_length {m : ℕ} (k : Fin (m + 1)) (xs : List (Fin (m + 1))) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k xs).length + xs.count k = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases ha : a = k
    · simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel, ha, List.count_cons_self] at *
      omega
    · simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel, ha] at *
      omega

/-- 概要：全ての空部分語への代入は指定値の削除（BF §1.2.4）。
方針：元の語で帰納し、Fin 0 のリストの先頭が常に空であることを使う。
規約：部分語の個数には条件を課さない。
使われ方：空語の分割の選び方に依存しない合成項の式。 -/
lemma substitute_nullary {m : ℕ} (k : Fin (m + 1)) (xs : List (Fin (m + 1)))
    (parts : List (List (Fin 0))) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs parts = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k xs := by
  induction xs generalizing parts with
  | nil => rfl
  | cons a xs ih =>
    have hz (l : List (Fin 0)) : l = [] := by
      cases l with
      | nil => rfl
      | cons a _ => exact Fin.elim0 a
    by_cases ha : a = k
    · simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, ha, hz, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel, ih]
    · simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, ha, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotLabel, ih]

/-- 概要：実際の nullary 合成置換の逆行は元の逆行の指定値削除（BF §1.5.7）。
方針：既存の一出現代入の式に空語代入の公式を適用する。
規約：内側置換は空集合の任意の置換。
使われ方：nullary の table reduction 比較で各実際の行を削除行へ移す。 -/
lemma permutationComposition_inverse_row_nullary {m : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0)) (k : Fin (m + 1)) :
    List.ofFn (_root_.SerrePositivity.EInfinity.BarrattEccles.permutationComposition m 0 k σ τ).symm =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k (List.ofFn σ.symm) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_inverse_row_substitute, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_nullary]

/-- 概要：空語との合成項は分割によらず削除語の正規化（BF §1.2.4）。
方針：compositeGenerator の代入を空語削除の式へ置き換える。
規約：退化語は既存の正規化で零。
使われ方：一出現の場合の有限和を評価する。 -/
lemma compositeGenerator_nullary (A : Type u) [CommRing A] {m d : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (0 + 0)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeGenerator A u v k r =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator A (d := d + 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k (List.ofFn u.val)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeGenerator _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_nullary]

/-- 概要：指定値が一回の場合の空語との合成は削除語の正規化（BF §1.2.4）。
方針：空語の一部分割の一意性と次数零の正符号で有限和を評価する。
規約：削除により隣接重複が生じた場合も同じ等式。
使われ方：nullary 合成保存の一出現の場合を実際の削除表へ比較する。 -/
lemma compositionOnWords_nullary_of_count_eq_one (A : Type u) [CommRing A] {m d : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (k : Fin (m + 1))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords A u v k =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator A (d := d + 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k (List.ofFn u.val)) := by
  let _ : Unique (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (0 + 0)) := by
    rw [h]
    exact ⟨⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.single 0⟩, fun r => r.eq_single⟩
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords, Fintype.sum_unique, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSign_inner_degree_zero,
    one_smul, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeGenerator_nullary]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
