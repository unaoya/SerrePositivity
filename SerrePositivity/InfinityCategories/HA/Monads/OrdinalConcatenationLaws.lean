module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalConcatenation

/-!
概要：順序和と端点共有の貼り合わせの二つの全結合則を値で示す。
方針：三つの区間のどこに点が属するかで分け、個数の等式をHEqで保持する。
規約：空の順序和の因子も含む。使われ方：HA Proposition 4.7.3.3、
Riehl–Verity Remark 3.3.8 の残る混合水平結合則。
Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {m n p q r s : ℕ}

/-- 概要：非空な左因子の順序和を、次元の和の表示へ輸送する。
方針：Fin.castOrderIsoで同じ値の射を移す。
規約：新しい合成ではなくordinalAppendの添字の輸送。使われ方：Riehl–Verity Remark 3.3.8。 -/
def ordinalAppendNonempty (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin p →o Fin q) : Fin (m + p + 1) →o Fin (n + q + 1) :=
  (Fin.castOrderIso (Nat.succ_add n q)).toOrderEmbedding.toOrderHom.comp
    ((ordinalAppend f g).comp
      (Fin.castOrderIso (Nat.succ_add m p).symm).toOrderEmbedding.toOrderHom)

/-- 概要：次元の表示への輸送は自然数の値を変えない。
方針：Finの等式輸送の定義。規約：始域の点も同じ値で戻す。
使われ方：HA Proposition 4.7.3.3 の水平合成の型の輸送。 -/
lemma ordinalAppendNonempty_val (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin p →o Fin q) (i : Fin (m + p + 1)) :
    (ordinalAppendNonempty f g i).val =
      (ordinalAppend f g ⟨i.val, by have := i.isLt; omega⟩).val := rfl

/-- 概要：共有点までの任意の点での貼り合わせの値。
方針：左の枝を使う。規約：同じ有限区間の点。
使われ方：Riehl–Verity Remark 3.3.8 の三重合成の計算。 -/
lemma ordinalGlue_val_of_le (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (i : Fin (m + p + 1)) (hi : i.val ≤ m) :
    (ordinalGlue f g i).val = (f ⟨i.val, by omega⟩).val := by
  simp [ordinalGlue, hi]

/-- 概要：共有点の後の任意の点での貼り合わせの値。
方針：右の枝を使う。規約：左の次元だけ値をずらす。
使われ方：Riehl–Verity Remark 3.3.8 の三重合成の計算。 -/
lemma ordinalGlue_val_of_lt (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (i : Fin (m + p + 1)) (hi : m < i.val) :
    (ordinalGlue f g i).val = n + (g ⟨i.val - m, by have := i.isLt; omega⟩).val := by
  simp [ordinalGlue, show ¬ i.val ≤ m by omega]

/-- 概要：前に順序和を足す操作と、後で端点を共有する操作の全結合則。
方針：三つの区間の各点で値を照合し、個数の加法の結合則を輸送する。
規約：前の因子は空も許す。使われ方：Riehl–Verity Remark 3.3.8 の水平結合則。 -/
lemma ordinalAppend_glue_assoc (f : Fin m →o Fin n)
    (g : Fin (p + 1) →o Fin (q + 1)) (h : Fin (r + 1) →o Fin (s + 1)) :
    HEq (ordinalGlue (m := m + p) (n := n + q)
      (ordinalAppend (m := m) (n := n) (p := p + 1) (q := q + 1) f g) h)
      (ordinalAppend f (ordinalGlue g h)) := by
  apply ordinalHom_hext (by omega) (by omega)
  intro i j hij
  by_cases hi : i.val ≤ m + p
  · rw [ordinalGlue_val_of_le _ _ i hi]
    by_cases hl : i.val < m
    · calc
        _ = (f ⟨i.val, hl⟩).val := ordinalAppend_val_left f g _ hl
        _ = (f ⟨j.val, by omega⟩).val :=
          congrArg (fun k : Fin m => (f k).val) (Fin.ext hij)
        _ = _ := (ordinalAppend_val_left f (ordinalGlue g h) j (by omega)).symm
    · have hk : (⟨i.val - m, by omega⟩ : Fin (p + 1)) = ⟨j.val - m, by omega⟩ :=
        Fin.ext (by change i.val - m = j.val - m; omega)
      calc
        _ = n + (g ⟨i.val - m, by omega⟩).val :=
          ordinalAppend_val_right f g _ (by change m ≤ i.val; omega)
        _ = n + (g ⟨j.val - m, by omega⟩).val :=
          congrArg (fun k : Fin (p + 1) => n + (g k).val) hk
        _ = n + (ordinalGlue g h ⟨j.val - m, by have := j.isLt; omega⟩).val := by
          rw [ordinalGlue_val_of_le g h _ (by change j.val - m ≤ p; omega)]
        _ = _ := (ordinalAppend_val_right f (ordinalGlue g h) j (by omega)).symm
  · rw [ordinalGlue_val_of_lt _ _ i (by omega),
      ordinalAppend_val_right _ _ j (by omega),
      ordinalGlue_val_of_lt _ _ _ (by change p < j.val - m; omega)]
    dsimp only
    have he : i.val - (m + p) = j.val - m - p := by omega
    simp only [he, Nat.add_assoc]

/-- 概要：先に端点を共有する操作と、後ろに順序和を足す操作の全結合則。
方針：次元の表示への輸送の値を変えず、三つの区間で照合する。
規約：後ろの因子は空も許す。使われ方：Riehl–Verity Remark 3.3.8 の水平結合則。 -/
lemma ordinalGlue_append_assoc (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (h : Fin r →o Fin s) :
    HEq (ordinalAppendNonempty (ordinalGlue f g) h)
      (ordinalGlue f (ordinalAppendNonempty g h)) := by
  apply ordinalHom_hext (by omega) (by omega)
  intro i j hij
  rw [ordinalAppendNonempty_val]
  by_cases hi : i.val < m + p + 1
  · rw [ordinalAppend_val_left _ _ _ (by exact hi)]
    by_cases hl : i.val ≤ m
    · rw [ordinalGlue_val_of_le _ _ _ (by exact hl), ordinalGlue_val_of_le _ _ j (by omega)]
      dsimp only
      congr 2
      exact Fin.ext hij
    · rw [ordinalGlue_val_of_lt _ _ _ (by change m < i.val; omega),
        ordinalGlue_val_of_lt _ _ j (by omega),
        ordinalAppendNonempty_val,
        ordinalAppend_val_left _ _ _ (by change j.val - m < p + 1; omega)]
      dsimp only
      have hk : (⟨i.val - m, by omega⟩ : Fin (p + 1)) = ⟨j.val - m, by omega⟩ :=
        Fin.ext (by change i.val - m = j.val - m; omega)
      exact congrArg (fun k : Fin (p + 1) => n + (g k).val) hk
  · rw [ordinalAppend_val_right _ _ _ (by change m + p + 1 ≤ i.val; omega),
      ordinalGlue_val_of_lt _ _ j (by omega),
      ordinalAppendNonempty_val, ordinalAppend_val_right _ _ _ (by change p + 1 ≤ j.val - m; omega)]
    dsimp only
    have he : i.val - (m + (p + 1)) = j.val - m - (p + 1) := by omega
    simp only [he, Nat.add_assoc]

end SerrePositivity.InfinityCategories.HA.Monads
