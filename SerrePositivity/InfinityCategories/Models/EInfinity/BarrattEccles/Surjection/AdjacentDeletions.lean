module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Deletion

/-!
模型。文献の定義との比較は後で
# 隣接同値を持つ語の一文字削除

概要：Berger–Fresse §1.2.3・§1.4.4 の退化語の削除項を比較する。
方針：隣接同値のどちらを削除しても同じ語となり、他の削除では隣接同値が残る。
規約：語は任意であり、全射性を要求しない。
使われ方：退化語の境界の二項の相殺と残りの項の消滅を示す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：削除位置を飛ばす添字の自然数値（BF §1.2.3）。
方針：削除位置より前後の二分岐を評価する。
規約：位置より前なら不変、それ以後なら 1 を加える。
使われ方：削除前後での隣接位置を比較する。 -/
lemma succAbove_val_eq {l : ℕ} (p : Fin (l + 1)) (k : Fin l) :
    (p.succAbove k).val = if k.val < p.val then k.val else k.val + 1 := by
  by_cases h : k.val < p.val
  · rw [Fin.succAbove_of_castSucc_lt p k h, ite_eq_left h]
    rfl
  · rw [Fin.succAbove_of_le_castSucc p k (Nat.le_of_not_gt h), ite_eq_right h]
    rfl

/-- 概要：隣接する同値のどちらを削除しても同じ語（BF §1.4.4）。
方針：各位置が隣接対より前・その場所・後である場合を比較する。
規約：出力語の長さは一つ小さい。
使われ方：逆符号の二つの削除項の値が等しいことを保証する。 -/
lemma erase_adjacent_eq {n l : ℕ} (u : Fin (l + 1) → Fin n) (i j : Fin (l + 1))
    (hij : i.val + 1 = j.val) (he : u i = u j) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u j := by
  funext k
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_apply]
  by_cases hk : k.val < i.val
  · rw [Fin.succAbove_of_castSucc_lt i k hk,
      Fin.succAbove_of_castSucc_lt j k (by change k.val < j.val; omega)]
  · by_cases heq : k.val = i.val
    · have h₁ : i.succAbove k = j := by
        apply Fin.ext
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.succAbove_val_eq, ite_eq_right hk]
        omega
      have h₂ : j.succAbove k = i := by
        apply Fin.ext
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.succAbove_val_eq, ite_eq_left (by omega)]
        exact heq
      rw [h₁, h₂]
      exact he.symm
    · rw [Fin.succAbove_of_le_castSucc i k (by change i.val ≤ k.val; omega),
        Fin.succAbove_of_le_castSucc j k (by change j.val ≤ k.val; omega)]

/-- 概要：削除で残る二つの隣接位置の逆像も隣接（BF §1.4.4）。
方針：二位置の順序を保ち、飛ばされた位置をまたぐなら元の差が 2 以上となる。
規約：削除した位置自身は逆像に現れない。
使われ方：他の文字を削除しても退化な対が残ることを示す。 -/
lemma succAbove_lifts_adjacent {l : ℕ} (p i j : Fin (l + 1)) (a b : Fin l)
    (hij : i.val + 1 = j.val) (ha : p.succAbove a = i) (hb : p.succAbove b = j) :
    a.val + 1 = b.val := by
  have hab : a < b := by
    apply (Fin.succAboveOrderEmb p).strictMono.lt_iff_lt.mp
    change p.succAbove a < p.succAbove b
    rw [ha, hb]
    change i.val < j.val
    omega
  have hva := congrArg (fun k : Fin (l + 1) => k.val) ha
  have hvb := congrArg (fun k : Fin (l + 1) => k.val) hb
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.succAbove_val_eq] at hva hvb
  have hab' : a.val < b.val := hab
  by_cases h₁ : a.val < p.val <;> by_cases h₂ : b.val < p.val <;>
    simp only [h₁, h₂, ↓reduceIte] at hva hvb <;> omega

/-- 概要：隣接同値以外を削除した語は退化したまま（BF §1.4.4）。
方針：隣接対の二位置を削除の前合成の像で戻す。
規約：削除位置は隣接対のどちらとも異なる。
使われ方：退化語の削除和で相殺対以外の項を零にする。 -/
lemma erase_not_nondegenerate_of_adjacent_eq {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i j k : Fin (l + 1)) (hij : i.val + 1 = j.val) (he : u i = u j)
    (hki : k ≠ i) (hkj : k ≠ j) : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u k) := by
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hki.symm
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hkj.symm
  intro hnd
  apply hnd a b (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.succAbove_lifts_adjacent k i j a b hij ha hb)
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_apply, ha, hb] using he

/-- 概要：非全射な語の削除は非全射（BF §1.2.3）。
方針：削除後の全射性から元の全射性を合成で導く。
規約：削除位置や非退化性によらない。
使われ方：非全射語の全ての境界項を零にする。 -/
lemma not_surjective_erase {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (hu : ¬ Function.Surjective u) (i : Fin (l + 1)) :
    ¬ Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) := by
  intro h
  apply hu
  intro a
  obtain ⟨k, hk⟩ := h a
  exact ⟨i.succAbove k, hk⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
