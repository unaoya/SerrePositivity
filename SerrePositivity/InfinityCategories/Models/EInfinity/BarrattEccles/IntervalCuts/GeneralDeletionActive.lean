module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GeneralDeletionCaesuras
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.DeletedActivePositions

/-!
模型。文献の定義との比較は後で
# 退化元切断にも使える削除後の活動集合

概要：Berger–Fresse §2.2.7 の実際の削除語の交換指数を元の活動集合の一位置削除へ移す。
方針：区切り自身の削除と最終出現の削除を分け、一般の区切り削除公式を使う。
規約：元切断の非零性を仮定せず、削除後の切断の非零性だけを符号比較に使う。
使われ方：非切断点障害の交換対の実際の切断符号の反対性。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：区切り自身の削除後の活動集合の像は元の集合からその位置を除いたもの（BF §2.2.7）。
方針：削除後の区切りの保存と切断点の保持を使う。
規約：元切断は退化していてよい。
使われ方：二位置とも区切りである交換対の符号比較。 -/
lemma activePositions_erase_caesura_image {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q).image i.succAbove =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u (i.succAbove q)).erase i := by
  ext b
  simp only [Finset.mem_image, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions, Finset.mem_insert, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · rintro ⟨a, ha | ha, rfl⟩
    · subst a
      exact ⟨Fin.succAbove_ne i q, Or.inl rfl⟩
    · exact ⟨Fin.succAbove_ne i a, Or.inr ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_erase_of_caesura u i hi a).mp ha)⟩
  · rintro ⟨hbi, hb⟩
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hbi
    refine ⟨a, ?_, ha⟩
    rcases hb with hb | hb
    · exact Or.inl (Fin.succAbove_right_injective (ha.trans hb))
    · right
      apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_erase_of_caesura u i hi a).mpr
      simpa only [ha] using hb

/-- 概要：最終出現削除後の活動集合の像は元から直前同色の区切りを除いたもの（BF §2.2.7）。
方針：失われる区切りの一般公式を使い、削除位置自身は元の活動集合に属さないことを使う。
規約：直前同色位置が切断点でないことを要求する。
使われ方：一位置だけが区切りである交換対を同じ活動集合へ戻す。 -/
lemma activePositions_erase_final_image {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i a : Fin (l + 1)) (q : Fin l) (hai : a < i) (hu : u a = u i)
    (hi : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i) (hgap : ∀ b, a < b → b < i → u b ≠ u i)
    (hpa : i.succAbove q ≠ a) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q).image i.succAbove =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u (i.succAbove q)).erase a := by
  have hiS : i ∉ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u (i.succAbove q) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with he | hc
    · exact Fin.ne_succAbove i q he
    · exact hi (Finset.mem_filter.mp hc).2
  ext b
  simp only [Finset.mem_image, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions, Finset.mem_insert, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · rintro ⟨c, hc | hc, rfl⟩
    · subst c
      exact ⟨hpa, Or.inl rfl⟩
    · have ht := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_erase_final u a i hai hu hi hgap c).mp hc
      exact ⟨ht.2, Or.inr ht.1⟩
  · rintro ⟨hba, hb⟩
    have hbi : b ≠ i := by
      intro he
      have hbmem : b ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u (i.succAbove q) :=
        Finset.mem_insert.mpr (hb.imp_right (fun hc => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hc⟩))
      exact hiS (he ▸ hbmem)
    obtain ⟨c, hc⟩ := Fin.exists_succAbove_eq hbi
    refine ⟨c, ?_, hc⟩
    rcases hb with hb | hb
    · exact Or.inl (Fin.succAbove_right_injective (hc.trans hb))
    · right
      apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_erase_final u a i hai hu hi hgap c).mpr
      simpa only [hc] using And.intro hb hba

/-- 概要：削除語の切断符号は活動集合の元位置への像の逆転数（BF §2.2.7）。
方針：削除後の非零切断の符号公式と順序単射の逆転数保存を使う。
規約：元切断の非零性は不要。
使われ方：一般の削除集合公式を実際の切断符号へ渡す。 -/
lemma edgeSign_erase_image {n l : ℕ} (u : Fin (l + 1) → Fin n) (i : Fin (l + 1))
    (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q = (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q).image i.succAbove) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_eq_inversionCount h, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_image u i.succAbove
    (Fin.strictMono_succAbove i)]
  rfl

/-- 概要：区切り削除後の実際の切断符号はその位置を除いた元活動集合の符号（BF §2.2.7）。
方針：活動集合の像の公式を切断符号へ適用する。
規約：削除後だけ非零となる場合も含む。
使われ方：両位置が区切りである交換対の係数計算。 -/
lemma edgeSign_erase_caesura {n l : ℕ} (u : Fin (l + 1) → Fin n) (i : Fin (l + 1))
    (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q) (hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q =
      (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u (i.succAbove q)).erase i) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_erase_image u i q h, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_erase_caesura_image u i q hi]

/-- 概要：最終出現削除後の実際の切断符号は直前同色を除いた活動集合の符号（BF §2.2.7）。
方針：最終出現削除の活動集合の像を使う。
規約：切断点と直前同色位置が異なる場合。
使われ方：最終出現とその直前の削除の切断符号を一致させる。 -/
lemma edgeSign_erase_final {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i a : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q)
    (hai : a < i) (hu : u a = u i) (hi : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i)
    (hgap : ∀ b, a < b → b < i → u b ≠ u i) (hpa : i.succAbove q ≠ a) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q =
      (-1 : ℤ) ^ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u (i.succAbove q)).erase a) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_erase_image u i q h, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_erase_final_image u i a q hai hu hi hgap hpa]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
