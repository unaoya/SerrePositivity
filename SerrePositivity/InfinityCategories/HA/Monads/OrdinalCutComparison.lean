module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalConcatenationLaws

/-!
概要：順序和の切れ目と端点共有の共有点を有限単調射の表示から回収する。
方針：実区間表示のGalois対応を、切れ目より左にある点の条件に書き換える。
規約：空も許す点の個数を用いる。使われ方：Riehl–Verity Proposition 3.1.10・Remark 3.3.8、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の分解の一意性。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：有限順序集合の切れ目は、その左にある全ての点で区別できる。
方針：二つの切れ目が異なれば、小さい方と同じ値の点を選ぶ。
規約：最大の切れ目も含む。使われ方：Riehl–Verity Proposition 3.1.10 の切れ目の回収。 -/
lemma ordinalCut_ext {m : ℕ} (a b : Fin (m + 1))
    (h : ∀ i : Fin m, i.val < a.val ↔ i.val < b.val) : a = b := by
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hab
  · have hi : a.val < m := by have := b.isLt; omega
    have hh := h ⟨a.val, hi⟩
    change a.val < a.val ↔ a.val < b.val at hh
    omega
  · have hi : b.val < m := by have := a.isLt; omega
    have hh := h ⟨b.val, hi⟩
    change b.val < a.val ↔ b.val < b.val at hh
    omega

/-- 概要：区間表示で戻した切れ目より左にあることは、元の像が切れ目より左にあること。
方針：最大元付加と実左随伴のGalois対応を使う。
規約：元の集合は空も許す。使われ方：Riehl–Verity Proposition 3.1.10 の切れ目の移送。 -/
lemma ordinalIntervalMap_cut_iff {m n : ℕ} (f : Fin m →o Fin n)
    (i : Fin m) (c : Fin (n + 1)) :
    i.val < (ordinalIntervalMap f c).val ↔ (f i).val < c.val := by
  have h := (ordinalIntervalMap_gc f).lt_iff_lt (a := c) (b := i.castSucc)
  simpa only [ordinalAdjoinTop_castSucc, Fin.lt_def, Fin.val_castSucc] using h

/-- 概要：全点での左右の分割条件が与えられれば、戻す切れ目は一意。
方針：切れ目の外延性と実区間表示の比較を使う。
規約：切れ目自体をデータとして指定する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma ordinalIntervalMap_cut_unique {m n : ℕ} (f : Fin m →o Fin n)
    (a : Fin (m + 1)) (b : Fin (n + 1))
    (h : ∀ i : Fin m, i.val < a.val ↔ (f i).val < b.val) :
    ordinalIntervalMap f b = a := by
  apply ordinalCut_ext
  intro i
  exact (ordinalIntervalMap_cut_iff f i b).trans (h i).symm

/-- 概要：順序和の二因子の間の切れ目は、実区間表示で同じ切れ目へ戻る。
方針：左因子と右因子の全点で左右の分割条件を照合する。
規約：空の因子も含む。使われ方：Riehl–Verity Proposition 3.1.10 のplusの切れ目。 -/
lemma ordinalAppend_cut {m n p q : ℕ} (f : Fin m →o Fin n) (g : Fin p →o Fin q) :
    ordinalIntervalMap (ordinalAppend f g) ⟨n, by omega⟩ = ⟨m, by omega⟩ := by
  apply ordinalIntervalMap_cut_unique
  intro i
  change i.val < m ↔ (ordinalAppend f g i).val < n
  by_cases hi : i.val < m
  · rw [ordinalAppend_val_left f g i hi]
    have := (f ⟨i.val, hi⟩).isLt
    omega
  · rw [ordinalAppend_val_right f g i (by omega)]
    omega

/-- 概要：端点共有の射は、元の共有点を同じ共有点へ送る。
方針：共有点までの左の包含と左因子の最大元保存を使う。
規約：右因子の値を勝手に仮定しない。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma ordinalGlue_shared {m n p q : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (hf : f (Fin.last m) = Fin.last n) :
    ordinalGlue f g ⟨m, by omega⟩ = ⟨n, by omega⟩ := by
  apply Fin.ext
  have h := ordinalGlue_val_left f g (Fin.last m)
  simpa only [hf, Fin.val_last] using h

/-- 概要：順序和の表示へ係数を移しても、合成から因子の切れ目を回収できる。
方針：個数と射を同一視し、既存の順序和の切れ目を使う。
規約：元の型の切れ目の値を保持する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma ordinalCut_of_append_profile {a b m n p q : ℕ} (ha : a = m + p) (hb : b = n + q)
    (H : Fin a →o Fin b) (f : Fin m →o Fin n) (g : Fin p →o Fin q)
    (h : HEq H (ordinalAppend f g)) (c : Fin (a + 1)) (d : Fin (b + 1))
    (hc : c.val = m) (hd : d.val = n) : ordinalIntervalMap H d = c := by
  subst a
  subst b
  have hH : H = ordinalAppend f g := eq_of_heq h
  subst H
  have hC : c = ⟨m, by omega⟩ := Fin.ext hc
  have hD : d = ⟨n, by omega⟩ := Fin.ext hd
  rw [hC, hD]
  exact ordinalAppend_cut f g

/-- 概要：端点共有の表示へ係数を移しても、合成は共有点を保持する。
方針：個数と射を同一視し、実際の左因子の最大元保存を使う。
規約：元の型の共有点の値を保持する。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma ordinalCut_of_glue_profile {a b m n p q : ℕ}
    (ha : a = m + p + 1) (hb : b = n + q + 1)
    (H : Fin a →o Fin b) (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (hf : f (Fin.last m) = Fin.last n)
    (h : HEq H (ordinalGlue f g)) (c : Fin a) (d : Fin b)
    (hc : c.val = m) (hd : d.val = n) : H c = d := by
  subst a
  subst b
  have hH : H = ordinalGlue f g := eq_of_heq h
  subst H
  have hC : c = ⟨m, by omega⟩ := Fin.ext hc
  have hD : d = ⟨n, by omega⟩ := Fin.ext hd
  rw [hC, hD]
  exact ordinalGlue_shared f g hf

end SerrePositivity.InfinityCategories.HA.Monads
