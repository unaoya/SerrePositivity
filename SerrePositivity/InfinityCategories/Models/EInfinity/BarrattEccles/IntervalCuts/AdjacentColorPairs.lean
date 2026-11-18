module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.AdjacentInversions

/-!
模型。文献の定義との比較は後で
# 活動色の二色対の個数

概要：Berger–Fresse §2.2.4 の隣接色交換で変わる逆転対の個数を計算する。
方針：活動位置で色が単射なら、指定二色の順序付き位置対は高々一つである。
規約：二色とも現れれば一つ、片方がなければ零。
使われ方：逆転数の変化を出力二因子の Koszul 符号へ移す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

/-- 概要：指定した二色を持つ位置対の有限集合（BF §2.2.4）。
方針：位置の小さい側を先に並べ、色の二つの順を許す。
規約：一つの非順序対を一回だけ数える。
使われ方：隣接色交換の逆転集合の対称差。 -/
def colorCrossPairs {n l : ℕ} (u : Fin l → Fin n) (s : Finset (Fin l)) (a b : Fin n) :
    Finset (Fin l × Fin l) :=
  (s ×ˢ s).filter (fun ij => ij.1 < ij.2 ∧
    ((u ij.1 = a ∧ u ij.2 = b) ∨ (u ij.1 = b ∧ u ij.2 = a)))

/-- 概要：二色の位置対の所属条件（BF §2.2.4）。
方針：積集合とフィルタの所属を展開する。
規約：両位置は指定集合内、位置順は狭義増加。
使われ方：色の単射性と存在の証明。 -/
lemma mem_colorCrossPairs {n l : ℕ} (u : Fin l → Fin n) (s : Finset (Fin l)) (a b : Fin n)
    (ij : Fin l × Fin l) : ij ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorCrossPairs u s a b ↔
      ij.1 ∈ s ∧ ij.2 ∈ s ∧ ij.1 < ij.2 ∧
        ((u ij.1 = a ∧ u ij.2 = b) ∨ (u ij.1 = b ∧ u ij.2 = a)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorCrossPairs, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- 概要：色が単射なら指定二色の位置対は高々一つ（BF §2.2.4）。
方針：同じ色順なら単射性、逆の色順なら位置の狭義順序で比較する。
規約：単射性は指定位置集合だけに要求する。
使われ方：対称差の濃度を零か一へ限定する。 -/
lemma colorCrossPairs_subsingleton {n l : ℕ} (u : Fin l → Fin n) (s : Finset (Fin l))
    (hu : Set.InjOn u s) (a b : Fin n) :
    Set.Subsingleton (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorCrossPairs u s a b : Set (Fin l × Fin l)) := by
  intro p hp q hq
  rcases (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.mem_colorCrossPairs u s a b p).mp hp with ⟨hp1, hp2, hplt, hp⟩
  rcases (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.mem_colorCrossPairs u s a b q).mp hq with ⟨hq1, hq2, hqlt, hq⟩
  rcases hp with ⟨hpa, hpb⟩ | ⟨hpb, hpa⟩ <;>
    rcases hq with ⟨hqa, hqb⟩ | ⟨hqb, hqa⟩
  · exact Prod.ext (hu hp1 hq1 (hpa.trans hqa.symm)) (hu hp2 hq2 (hpb.trans hqb.symm))
  · have he1 := hu hp1 hq2 (hpa.trans hqa.symm)
    have he2 := hu hp2 hq1 (hpb.trans hqb.symm)
    rw [he1, he2] at hplt
    exact False.elim (lt_asymm hplt hqlt)
  · have he1 := hu hp1 hq2 (hpb.trans hqb.symm)
    have he2 := hu hp2 hq1 (hpa.trans hqa.symm)
    rw [he1, he2] at hplt
    exact False.elim (lt_asymm hplt hqlt)
  · exact Prod.ext (hu hp1 hq1 (hpb.trans hqb.symm)) (hu hp2 hq2 (hpa.trans hqa.symm))

/-- 概要：異なる二色の位置対が存在する条件は両色の出現（BF §2.2.4）。
方針：出現位置を取り、互いに異なる二位置を小さい順に並べる。
規約：存在条件自体には色の単射性は不要。
使われ方：二色の対の濃度の零一判定。 -/
lemma colorCrossPairs_nonempty_iff {n l : ℕ} (u : Fin l → Fin n) (s : Finset (Fin l))
    (a b : Fin n) (hab : a ≠ b) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorCrossPairs u s a b).Nonempty ↔ a ∈ s.image u ∧ b ∈ s.image u := by
  constructor
  · rintro ⟨p, hp⟩
    rcases (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.mem_colorCrossPairs u s a b p).mp hp with ⟨hp1, hp2, _, hp⟩
    rcases hp with ⟨hpa, hpb⟩ | ⟨hpb, hpa⟩
    · exact ⟨Finset.mem_image.mpr ⟨p.1, hp1, hpa⟩, Finset.mem_image.mpr ⟨p.2, hp2, hpb⟩⟩
    · exact ⟨Finset.mem_image.mpr ⟨p.2, hp2, hpa⟩, Finset.mem_image.mpr ⟨p.1, hp1, hpb⟩⟩
  · rintro ⟨ha, hb⟩
    obtain ⟨i, hi, hai⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, hbj⟩ := Finset.mem_image.mp hb
    have hij : i ≠ j := by
      intro he
      exact hab (hai.symm.trans ((congrArg u he).trans hbj))
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact ⟨(i, j), (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.mem_colorCrossPairs u s a b _).mpr ⟨hi, hj, hij, Or.inl ⟨hai, hbj⟩⟩⟩
    · exact ⟨(j, i), (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.mem_colorCrossPairs u s a b _).mpr ⟨hj, hi, hji, Or.inr ⟨hbj, hai⟩⟩⟩

/-- 概要：色単射な集合の二色対の個数は両色が現れる指示関数（BF §2.2.4）。
方針：高々一つであることと存在の必要十分条件を結ぶ。
規約：指定二色は互いに異なる。
使われ方：隣接交換の切断符号を一つの零一指数へ直す。 -/
lemma card_colorCrossPairs {n l : ℕ} (u : Fin l → Fin n) (s : Finset (Fin l))
    (hu : Set.InjOn u s) (a b : Fin n) (hab : a ≠ b) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorCrossPairs u s a b).card = if a ∈ s.image u ∧ b ∈ s.image u then 1 else 0 := by
  by_cases h : a ∈ s.image u ∧ b ∈ s.image u
  · rw [ite_eq_left h]
    have hle := Finset.card_le_one.mpr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorCrossPairs_subsingleton u s hu a b)
    have hpos := Finset.card_pos.mpr ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorCrossPairs_nonempty_iff u s a b hab).mpr h)
    omega
  · rw [ite_eq_right h]
    apply Finset.card_eq_zero.mpr
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hn
    exact h ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.colorCrossPairs_nonempty_iff u s a b hab).mp hn)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
