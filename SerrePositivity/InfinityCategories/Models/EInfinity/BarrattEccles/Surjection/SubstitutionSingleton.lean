module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.HorizontalLabels
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SubstitutionOneSlot
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.PermutationStateSubstitution

/-!
模型。文献の定義との比較は後で
# 内側一文字の代入と水平ラベル写像

概要：Berger–Fresse §1.5.7 の最終内側状態で代入が外側全行の単射ラベル変更になることを示す。
方針：重複しない外側行で指定値を一文字へ置き換える。
規約：指定値が行内部にあってもよい。
使われ方：指定値の最終除外を跨ぐ最後の水平成分の出力計算。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：指定値のない語へ空の部分語列を渡すと水平ラベル像（BF §1.5.7）。
方針：既存 remainingLetters の復元と指定値のない語の代入を使う。
規約：内側の固定文字は出力に現れない。
使われ方：唯一の指定値を置き換えた後の外側後半を評価する。 -/
lemma substitute_no_slot_horizontalLabel {m n : ℕ} (k : Fin (m + 1)) (b : Fin n)
    (xs : List (Fin (m + 1))) (hk : k ∉ xs) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs [] = xs.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) := by
  have hv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters_values_of_not_mem k xs hk
  have hf : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs [] = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters k xs).map (remainingPosition m n k) := by
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters k xs).map Subtype.val) [] := by rw [hv]
      _ = _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_remaining_word k _ []
  have hm : xs.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters k xs).map (remainingPosition m n k) := by
    calc
      _ = ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.remainingLetters k xs).map Subtype.val).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) := by rw [hv]
      _ = _ := by simp only [List.map_map, Function.comp_def, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel_remaining]
  exact hf.trans hm.symm

/-- 概要：重複しない行への一文字代入は水平ラベル像そのもの（BF §1.5.7）。
方針：先頭が指定値なら残りに指定値はなく、他の先頭なら帰納する。
規約：指定値は行内部でも末尾でもよい。
使われ方：最終水平成分の全選択長さで同じラベル写像を使う。 -/
lemma substitute_singleton_nodup {m n : ℕ} (k : Fin (m + 1)) (b : Fin n)
    (xs : List (Fin (m + 1))) (hn : xs.Nodup) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k xs [[b]] = xs.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have hns := List.nodup_cons.mp hn
    by_cases ha : a = k
    · subst a
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_left rfl, List.headD_cons, List.tail_cons, List.map_cons,
        List.map_nil, List.singleton_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_no_slot_horizontalLabel k b xs hns.1,
        List.map_cons, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel_slot]
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute, dite_eq_right ha, ih hns.2, List.map_cons]
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel, dite_eq_right ha]

/-- 概要：内側可用行が一文字なら実際の合成行は外側可用行の水平ラベル像（BF §1.5.7）。
方針：全段階の実際の合成行の代入表示へ一文字代入を適用する。
規約：指定値の外側での除外済みかどうかを問わない。
使われ方：最終除外を跨ぐ水平行の選択語を計算する。 -/
lemma singleton_composite_available {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n)) (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner : List (Fin n)) (b : Fin n)
    (hinner : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available inner (List.ofFn τ.symm) = [b]) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner)
      (List.ofFn (permutationComposition m n k σ τ).symm) =
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available outer (List.ofFn σ.symm)).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_state_available_substitute, hinner]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute_singleton_nodup k b _ ((List.nodup_ofFn_ofInjective σ.symm.injective).filter _)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
