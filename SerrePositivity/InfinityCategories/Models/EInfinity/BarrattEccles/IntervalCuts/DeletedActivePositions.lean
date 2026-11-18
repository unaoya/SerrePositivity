module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletion
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ActiveSigns
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InversionCounts

/-!
模型。文献の定義との比較は後で
# 文字削除後の活動位置と交換指数

概要：Berger–Fresse §2.2.7 の削除後の活動位置を元の活動集合から一色を除いたものへ同定する。
方針：非零切断では各色が高々二回現れることを使い、削除後の区切りを特徴付ける。
規約：削除後の位置は succAbove で元の語へ戻し、切断点は残す。
使われ方：元の活動集合の一位置削除の符号を実際の削除語の切断符号へ移す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open scoped _root_.BigOperators

/-- 概要：非零切断で同色の二出現があれば他の同色位置はない（BF §2.2.1）。
方針：任意の位置を切断点の左右に分け、それぞれの単射性を使う。
規約：二出現の順序を固定する。
使われ方：反復色の一文字削除後にその色の区切りが消えることを示す。 -/
lemma occurrence_eq_one_of_two {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) (a b : Fin l) (hab : a < b) (hu : u a = u b)
    (j : Fin l) (hj : u j = u a) : j = a ∨ j = b := by
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.repeated_straddles h hab hu
  by_cases hjp : j ≤ p
  · exact Or.inl (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_left_injective h j a hjp hs.1.le hj)
  · exact Or.inr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_right_injective h j b (le_of_lt (lt_of_not_ge hjp)) hs.2.le
      (hj.trans hu))

/-- 概要：削除後の区切りは元の区切りから削除色を除いたもの（BF §2.2.7）。
方針：削除後の二出現を元へ持ち上げ、削除色なら三出現となる矛盾を使う。
規約：切断点を残す条件はこの区切り公式自体には不要。
使われ方：削除後の活動集合の元位置での像を計算する。 -/
lemma caesura_erase_iff_of_cut {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (p : Fin (l + 1)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) (i : Fin (l + 1)) (a : Fin l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) a ↔
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u (i.succAbove a) ∧ u (i.succAbove a) ≠ u i := by
  constructor
  · rintro ⟨b, hab, hb⟩
    have hab' := Fin.strictMono_succAbove i hab
    refine ⟨⟨i.succAbove b, hab', hb⟩, ?_⟩
    intro hi
    rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.occurrence_eq_one_of_two h _ _ hab' hb.symm i hi.symm with he | he
    · exact Fin.ne_succAbove i a he
    · exact Fin.ne_succAbove i b he
  · rintro ⟨⟨b, hab, hb⟩, hi⟩
    have hbi : b ≠ i := by intro he; subst b; exact hi hb.symm
    obtain ⟨c, hc⟩ := Fin.exists_succAbove_eq hbi
    refine ⟨c, ?_, ?_⟩
    · apply (Fin.strictMono_succAbove i).lt_iff_lt.mp
      rwa [hc]
    · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_apply, hc] using hb

/-- 概要：削除後の活動集合の像は元の活動集合から削除色を除いたもの（BF §2.2.7）。
方針：切断点と区切りに分け、区切りの削除公式と切断点の色の一意性を使う。
規約：切断点は削除の順序単射の像にある。
使われ方：削除前後の実際の活動集合を照合する。 -/
lemma activePositions_erase_image {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u (i.succAbove q)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q).image i.succAbove =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u (i.succAbove q)).filter (fun a => u a ≠ u i) := by
  have hp : u (i.succAbove q) ≠ u i := by
    intro he
    exact Fin.ne_succAbove i q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivot_unique h i he.symm)
  ext a
  simp only [Finset.mem_image, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨b, hb | hb, rfl⟩
    · subst b
      exact ⟨Or.inl rfl, hp⟩
    · have hc := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_erase_iff_of_cut u _ h i b).mp hb
      exact ⟨Or.inr hc.1, hc.2⟩
  · rintro ⟨ha, hc⟩
    have hai : a ≠ i := by intro he; subst a; exact hc rfl
    obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hai
    refine ⟨b, ?_, hb⟩
    rcases ha with ha | ha
    · left
      exact Fin.succAbove_right_injective (hb.trans ha)
    · right
      apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_erase_iff_of_cut u _ h i b).mpr
      simpa only [hb] using And.intro ha hc

/-- 概要：削除色の活動位置 a を指定すると削除後の像は元の集合から a を除いたもの（BF §2.2.7）。
方針：活動位置上の色の単射性によって一色の削除を一位置の削除へ直す。
規約：実際に削除する文字位置 i は最初・最後のどちらでもよい。
使われ方：有限逆転数の一位置削除公式へ接続する。 -/
lemma activePositions_erase_image_eq_erase {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u (i.succAbove q))
    (a : Fin (l + 1)) (ha : a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u (i.succAbove q)) (hua : u a = u i) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q).image i.succAbove =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u (i.succAbove q)).erase a := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_erase_image u i q h]
  ext b
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hb, hc⟩
    exact ⟨fun hba => hc (hba ▸ hua), hb⟩
  · rintro ⟨hba, hb⟩
    exact ⟨hb, fun hc => hba (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_injOn h hb ha (hc.trans hua.symm))⟩

/-- 概要：順序単射で位置を戻しても色の逆転数は変わらない（BF §2.2.4）。
方針：二つの有限和を像で添字替えし、順序の保存と反映を使う。
規約：任意の有限な位置集合。
使われ方：削除後の交換指数を元の位置集合の交換指数へ移す。 -/
lemma positionInversionCount_image {n l m : ℕ} (u : Fin m → Fin n)
    (ρ : Fin l → Fin m) (hρ : StrictMono ρ) (s : Finset (Fin l)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u (s.image ρ) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount (u ∘ ρ) s := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount
  rw [Finset.sum_image (fun _ _ _ _ he => hρ.injective he)]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_image (fun _ _ _ _ he => hρ.injective he)]
  apply Finset.sum_congr rfl
  intro b _
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm, hρ.lt_iff_lt, Function.comp_apply]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
