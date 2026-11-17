module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalImageCard
public import Mathlib.Order.Fin.Basic

/-!
概要：有限実辺の両端と像の個数から定まる変化量を、合成と実同型の検収に使う。
方針：像の個数の上下を自然数の等式・不等式に移す。
規約：原典の文字列の幅との全比較は別に行う。
使われ方：Riehl–Verity Proposition 4.2.15の実filtrationの幅の表示、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実面と実親の幅の法則。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：実辺の両端の個数の和から像の個数の二倍を除いた変化量。
方針：有限像の個数を使う。規約：空の有限順序集合も含む自然数。
使われ方：Riehl–Verity Proposition 4.2.15の実幅の計算。 -/
def ordinalMapVariation {m n : ℕ} (f : Fin m →o Fin n) : ℕ := m + n - 2 * ordinalImageCard f

/-- 概要：変化量0の実辺は両端の個数を保つ。
方針：像の個数の両方の上限を使う。規約：空も含む。
使われ方：Riehl–Verity §4.2の実非退化辺の変化量の正値。 -/
lemma ordinalMapVariation_zero_card {m n : ℕ} (f : Fin m →o Fin n)
    (h : ordinalMapVariation f = 0) : m = n := by
  have hm := ordinalImageCard_le_source f
  have hn := ordinalImageCard_le_target f
  unfold ordinalMapVariation at h
  omega

/-- 概要：変化量0の有限実単調射は全点の自然数の値を保つ。
方針：像の個数から単射性を得て、有限順序の厳密単調な自己写像の恒等性を使う。
規約：元の全有限点での等式。使われ方：Riehl–Verity §4.2の実同型の検収。 -/
lemma ordinalMapVariation_zero_val {m n : ℕ} (f : Fin m →o Fin n)
    (h : ordinalMapVariation f = 0) (i : Fin m) : (f i).val = i.val := by
  have hmn := ordinalMapVariation_zero_card f h
  subst n
  have hm := ordinalImageCard_le_source f
  have hc : ordinalImageCard f = m := by unfold ordinalMapVariation at h; omega
  have hi := (ordinalImageCard_eq_source_iff f).mp hc
  have he : (fun j => f j) = id := (f.monotone.strictMono_of_injective hi).eq_id
  exact congrArg Fin.val (congrFun he i)

/-- 概要：恒等実辺の変化量は0。
方針：恒等射の像の個数を単射性から計算する。規約：全有限個数。
使われ方：Riehl–Verity §4.2の実退化の幅の保存。 -/
lemma ordinalMapVariation_id (m : ℕ) : ordinalMapVariation (OrderHom.id (α := Fin m)) = 0 := by
  have hc := (ordinalImageCard_eq_source_iff (OrderHom.id (α := Fin m))).mpr Function.injective_id
  unfold ordinalMapVariation
  rw [hc]
  omega

/-- 概要：実二辺を合成した変化量は元の変化量の和以下。
方針：合成の像の下限と各像の両方の上限を合わせる。
規約：任意の実二射。使われ方：Riehl–Verity Proposition 4.2.15の実面の幅の比較。 -/
lemma ordinalMapVariation_comp_le {a b c : ℕ} (f : Fin a →o Fin b) (g : Fin b →o Fin c) :
    ordinalMapVariation (g.comp f) ≤ ordinalMapVariation f + ordinalMapVariation g := by
  have hf := ordinalImageCard_le_source f
  have hf' := ordinalImageCard_le_target f
  have hg := ordinalImageCard_le_source g
  have hg' := ordinalImageCard_le_target g
  have hc := ordinalImageCard_comp_lower_bound f g
  unfold ordinalMapVariation
  omega

/-- 概要：前半が全射なら実二辺の変化量は合成で加法的。
方針：前半の像は中間集合全体であり、合成の像は後半の像と一致する。
規約：元の全射性から計算する。使われ方：Riehl–Verity §4.2の実細分の幅の保存。 -/
lemma ordinalMapVariation_comp_of_surjective {a b c : ℕ} (f : Fin a →o Fin b)
    (g : Fin b →o Fin c) (hf : Function.Surjective f) :
    ordinalMapVariation (g.comp f) = ordinalMapVariation f + ordinalMapVariation g := by
  have hi := (ordinalImageCard_eq_target_iff f).mpr hf
  have ha := ordinalImageCard_le_source f
  have hb := ordinalImageCard_le_source g
  have hc := ordinalImageCard_le_target g
  unfold ordinalMapVariation
  rw [ordinalImageCard_comp_of_surjective f g hf, hi]
  omega

/-- 概要：実始点の個数は実終点の個数と変化量の和以下。
方針：像の個数は終点の個数以下であることを使う。
規約：空も含む。使われ方：Riehl–Verity §4.2の幅での実頂点の個数の上限。 -/
lemma ordinalMapVariation_source_le {m n : ℕ} (f : Fin m →o Fin n) :
    m ≤ n + ordinalMapVariation f := by
  have hn := ordinalImageCard_le_target f
  unfold ordinalMapVariation
  omega

/-- 概要：実終点の個数は実始点の個数と変化量の和以下。
方針：像の個数は始点の個数以下であることを使う。
規約：空も含む。使われ方：Riehl–Verity §4.2の幅での実頂点の個数の上限。 -/
lemma ordinalMapVariation_target_le {m n : ℕ} (f : Fin m →o Fin n) :
    n ≤ m + ordinalMapVariation f := by
  have hm := ordinalImageCard_le_source f
  unfold ordinalMapVariation
  omega

end SerrePositivity.InfinityCategories.HA.Monads
