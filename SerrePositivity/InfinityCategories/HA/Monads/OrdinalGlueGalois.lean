module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalConcatenationLaws

/-!
概要：区間表示の端点共有と、順序和のGalois随伴の射の比較。
方針：共有点の前後で分け、既存の区間表示・端点保存の随伴条件に戻す。
規約：順序和の空の因子も含む。存在を仮定せず、構成済みの有限随伴を使う。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の混合水平合成の比較。
Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {m n p q : ℕ}

/-- 概要：左に区間表示を貼る写像の右随伴は、元の射と右随伴の順序和。
方針：順序和の左・右で分け、区間表示と最小元保存の二つの随伴条件を使う。
規約：元の有限順序射は空も許す。使われ方：Riehl–Verity Remark 3.3.8 の左作用の比較。 -/
lemma ordinalGlue_interval_gc (f : Fin n →o Fin m)
    (g : Fin (p + 1) →o Fin (q + 1)) (hg : g 0 = 0) :
    GaloisConnection (ordinalGlue (ordinalIntervalMap f) g)
      (ordinalAppend (m := n) (n := m) (p := q + 1) (q := p + 1)
        f (ordinalRightAdjoint g hg)) := by
  intro i j
  change (ordinalGlue (ordinalIntervalMap f) g i).val ≤ j.val ↔
    i.val ≤ (ordinalAppend f (ordinalRightAdjoint g hg) j).val
  by_cases hj : j.val < n
  · rw [ordinalAppend_val_left f (ordinalRightAdjoint g hg) j hj]
    by_cases hi : i.val ≤ m
    · rw [ordinalGlue_val_of_le _ _ i hi]
      simpa only [ordinalAdjoinTop_castSucc, Fin.le_def, Fin.val_castSucc] using
        (ordinalIntervalMap_gc f) (⟨i.val, by omega⟩ : Fin (m + 1))
          (⟨j.val, hj⟩ : Fin n).castSucc
    · rw [ordinalGlue_val_of_lt _ _ i (by omega)]
      have := (f ⟨j.val, hj⟩).isLt
      omega
  · rw [ordinalAppend_val_right f (ordinalRightAdjoint g hg) j (by omega)]
    by_cases hi : i.val ≤ m
    · rw [ordinalGlue_val_of_le _ _ i hi]
      have := (ordinalIntervalMap f ⟨i.val, by omega⟩).isLt
      omega
    · rw [ordinalGlue_val_of_lt _ _ i (by omega)]
      have hc := (ordinalRightAdjoint_gc g hg)
        (⟨i.val - m, by have := i.isLt; omega⟩ : Fin (p + 1))
        (⟨j.val - n, by have := j.isLt; omega⟩ : Fin (q + 1))
      change (g ⟨i.val - m, by have := i.isLt; omega⟩).val ≤ j.val - n ↔
        i.val - m ≤ (ordinalRightAdjoint g hg ⟨j.val - n, by have := j.isLt; omega⟩).val at hc
      omega

/-- 概要：右に区間表示を貼る写像の左随伴は、左随伴と元の射の順序和。
方針：共有点の前後で分け、後半では区間表示の随伴条件の否定を使う。
規約：右の有限順序射は空も許す。使われ方：Riehl–Verity Remark 3.3.8 の右作用の比較。 -/
lemma ordinalGlue_interval_gc_right (f : Fin (m + 1) →o Fin (n + 1))
    (hf : f (Fin.last m) = Fin.last n) (g : Fin q →o Fin p) :
    GaloisConnection (ordinalAppendNonempty (ordinalLeftAdjoint f hf) g)
      (ordinalGlue f (ordinalIntervalMap g)) := by
  intro i j
  change (ordinalAppendNonempty (ordinalLeftAdjoint f hf) g i).val ≤ j.val ↔
    i.val ≤ (ordinalGlue f (ordinalIntervalMap g) j).val
  rw [ordinalAppendNonempty_val]
  by_cases hj : j.val ≤ m
  · rw [ordinalGlue_val_of_le _ _ j hj]
    by_cases hi : i.val < n + 1
    · rw [ordinalAppend_val_left (ordinalLeftAdjoint f hf) g ⟨i.val, by have := i.isLt; omega⟩ hi]
      exact (ordinalLeftAdjoint_gc f hf) (⟨i.val, hi⟩ : Fin (n + 1))
        (⟨j.val, by omega⟩ : Fin (m + 1))
    · rw [ordinalAppend_val_right (ordinalLeftAdjoint f hf) g
        ⟨i.val, by have := i.isLt; omega⟩ (by change n + 1 ≤ i.val; omega)]
      have := (f ⟨j.val, by omega⟩).isLt
      omega
  · rw [ordinalGlue_val_of_lt _ _ j (by omega)]
    by_cases hi : i.val < n + 1
    · rw [ordinalAppend_val_left (ordinalLeftAdjoint f hf) g ⟨i.val, by have := i.isLt; omega⟩ hi]
      have := (ordinalLeftAdjoint f hf ⟨i.val, hi⟩).isLt
      omega
    · rw [ordinalAppend_val_right (ordinalLeftAdjoint f hf) g
        ⟨i.val, by have := i.isLt; omega⟩ (by change n + 1 ≤ i.val; omega)]
      have hc := (ordinalIntervalMap_gc g)
        (⟨j.val - m, by have := j.isLt; omega⟩ : Fin (p + 1))
        (⟨i.val - (n + 1), by have := i.isLt; omega⟩ : Fin q).castSucc
      simp only [ordinalAdjoinTop_castSucc, Fin.le_def, Fin.val_castSucc] at hc
      change (ordinalIntervalMap g ⟨j.val - m, by have := j.isLt; omega⟩).val ≤
          i.val - (n + 1) ↔
        j.val - m ≤ (g ⟨i.val - (n + 1), by have := i.isLt; omega⟩).val at hc
      change m + 1 + (g ⟨i.val - (n + 1), by have := i.isLt; omega⟩).val ≤ j.val ↔
        i.val ≤ n + (ordinalIntervalMap g ⟨j.val - m, by have := j.isLt; omega⟩).val
      omega

/-- 概要：最大元の付加は有限Galois随伴を保つ。
方針：元の点同士では元の随伴条件、最後の点では最大性を使う。
規約：元の有限順序集合は空も許す。使われ方：Riehl–Verity Remark 3.3.8 の区間表示の照合。 -/
lemma ordinalAdjoinTop_gc {a b : ℕ} {f : Fin a →o Fin b} {g : Fin b →o Fin a}
    (h : GaloisConnection f g) : GaloisConnection (ordinalAdjoinTop f) (ordinalAdjoinTop g) := by
  intro i j
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last => simp only [ordinalAdjoinTop_last, le_refl]
    | cast j =>
      simp only [ordinalAdjoinTop_last, ordinalAdjoinTop_castSucc, Fin.le_def,
        Fin.val_last, Fin.val_castSucc]
      have := j.isLt
      have := (g j).isLt
      omega
  | cast i =>
    cases j using Fin.lastCases with
    | last =>
      simp only [ordinalAdjoinTop_last, ordinalAdjoinTop_castSucc]
      constructor <;> intro _ <;> exact Fin.le_last _
    | cast j =>
      simpa only [ordinalAdjoinTop_castSucc, Fin.castSucc_le_castSucc_iff] using h i j

/-- 概要：最小元保存の右随伴の区間表示は元の射の最大元付加。
方針：最大元付加のGalois随伴と、同じ右随伴を持つ左随伴の一意性を使う。
規約：実際に構成済みの右随伴。使われ方：Riehl–Verity Remark 3.3.8 の混合合成の比較。 -/
lemma ordinalIntervalMap_rightAdjoint (g : Fin (p + 1) →o Fin (q + 1)) (hg : g 0 = 0) :
    ordinalIntervalMap (ordinalRightAdjoint g hg) = ordinalAdjoinTop g := by
  apply OrderHom.ext
  funext i
  exact (ordinalIntervalMap_gc (ordinalRightAdjoint g hg)).l_unique
    (ordinalAdjoinTop_gc (ordinalRightAdjoint_gc g hg)) (fun _ => rfl)

end SerrePositivity.InfinityCategories.HA.Monads
