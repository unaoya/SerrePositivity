module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InversionReindex

/-!
模型。文献の定義との比較は後で
# 前後二つの活動位置ブロックの逆転数

概要：Berger–Fresse §2.2.4・§2.2.6 の切断点色への挿入の交換指数を二ブロックへ分ける。
方針：非交差な有限集合の二重和を内部二項と交差項へ分ける。
規約：前方全位置が後方全位置より小さい場合を扱う。
使われ方：外側の切断点を内側活動位置列で置換した合成切断の符号。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

/-- 概要：前後二ブロックの逆転数は内部二項と前から後への交差項の和（BF §2.2.4）。
方針：二重和の両添字を非交差な和集合で分け、逆向きの交差を位置順で消す。
規約：色は単射でなくてもよい。
使われ方：挿入した内側活動列と外側残り活動列の逆転数の比較。 -/
lemma positionInversionCount_ordered_union {n l : ℕ} (u : Fin l → Fin n)
    (s t : Finset (Fin l)) (hst : ∀ i ∈ s, ∀ j ∈ t, i < j) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u (s ∪ t) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u s +
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u t + ∑ i ∈ s, ∑ j ∈ t, if u j < u i then 1 else 0 := by
  have hd : Disjoint s t := Finset.disjoint_left.mpr (fun i hi hj => lt_irrefl i (hst i hi i hj))
  have hz : (∑ i ∈ t, ∑ j ∈ s, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u i j) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_right (fun h => lt_asymm (hst j hj i hi) h.1)
  have hc : (∑ i ∈ s, ∑ j ∈ t, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u i j) =
      ∑ i ∈ s, ∑ j ∈ t, if u j < u i then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm, hst i hi j hj, true_and]
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount
  simp_rw [Finset.sum_union hd]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hz, hc]
  omega

/-- 概要：二つの単射像ブロックの逆転数は元の二逆転数と一様な交差数（BF §2.2.6）。
方針：内部寄与を像から戻し、各後方位置と逆転する前方位置を数える。
規約：交差条件 P は前方位置だけに依存する。
使われ方：切断点色への挿入で内側活動数倍の交差指数を得る。 -/
lemma positionInversionCount_ordered_images {n l n' l' n'' l'' : ℕ}
    (u : Fin l → Fin n) (v : Fin l' → Fin n') (w : Fin l'' → Fin n'')
    (s : Finset (Fin l)) (t : Finset (Fin l')) (f : Fin l → Fin l'')
    (g : Fin l' → Fin l'') (hf : Set.InjOn f s) (hg : Set.InjOn g t)
    (horder : ∀ i ∈ s, ∀ j ∈ t, f i < g j)
    (hfterm : ∀ i ∈ s, ∀ j ∈ s,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm w (f i) (f j) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u i j)
    (hgterm : ∀ i ∈ t, ∀ j ∈ t,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm w (g i) (g j) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm v i j)
    (P : Fin l → Prop) [DecidablePred P]
    (hcross : ∀ i ∈ s, ∀ j ∈ t, w (g j) < w (f i) ↔ P i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount w (s.image f ∪ t.image g) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u s + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount v t +
        t.card * (s.filter P).card := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_ordered_union w _ _ (by
    intro i hi j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
    exact horder a ha b hb), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_image_of_terms u w s f hf hfterm,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_image_of_terms v w t g hg hgterm]
  congr 1
  rw [Finset.sum_image hf]
  calc
    _ = ∑ i ∈ s, t.card * (if P i then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_image hg]
      have hs : (∑ j ∈ t, if w (g j) < w (f i) then 1 else 0) =
          ∑ j ∈ t, if P i then 1 else 0 :=
        Finset.sum_congr rfl (fun j hj => if_congr (hcross i hi j hj) rfl rfl)
      rw [hs]
      by_cases hp : P i <;> simp only [hp, ite_true, ite_false, Finset.sum_const,
        smul_eq_mul, mul_one, mul_zero]
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_boole]; rfl

/-- 概要：末尾の活動位置を除く逆転差はその色より大きい色の個数（BF §2.2.4）。
方針：元集合を末尾以外と末尾一項の前後ブロックへ分ける。
規約：末尾は集合の最大元であればよい。
使われ方：切断点を内側活動列で置き換える前の外側逆転数。 -/
lemma positionInversionCount_last {n l : ℕ} (u : Fin l → Fin n) (s : Finset (Fin l))
    (p : Fin l) (hp : p ∈ s) (hmax : ∀ j ∈ s, j ≤ p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u s = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u (s.erase p) +
      ((s.erase p).filter (fun j => u p < u j)).card := by
  have hs : s.erase p ∪ {p} = s := by
    ext j
    by_cases hj : j = p
    · subst j; simp only [Finset.mem_union, Finset.mem_erase, ne_eq, not_true_eq_false,
        false_and, Finset.mem_singleton, or_true, hp]
    · simp only [Finset.mem_union, Finset.mem_erase, hj, ne_eq, not_false_eq_true, true_and,
        Finset.mem_singleton, or_false]
  have hz : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u {p} = 0 := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount, Finset.sum_singleton, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm,
      lt_self_iff_false, false_and, ite_false]
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_ordered_union u (s.erase p) {p} (by
    intro i hi j hj
    have hj' : j = p := Finset.mem_singleton.mp hj
    subst j
    exact lt_of_le_of_ne (hmax i (Finset.mem_erase.mp hi).2) (Finset.mem_erase.mp hi).1)
  simp only [hs, hz, Nat.add_zero, Finset.sum_singleton] at H
  simpa only [Finset.sum_boole, Nat.cast_id] using H

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
