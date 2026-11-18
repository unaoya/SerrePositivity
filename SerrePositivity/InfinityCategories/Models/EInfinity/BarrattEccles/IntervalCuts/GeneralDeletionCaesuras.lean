module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletion
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DeletionSigns

/-!
模型。文献の定義との比較は後で
# 一文字削除後の区切りの一般公式

概要：Berger–Fresse §1.2.3・§2.2.7 の区切り集合を退化元切断にも使える形で計算する。
方針：削除後の将来の同色出現を元の削除位置以外の出現へ戻す。
規約：元の切断の非零性を仮定せず、同色の直前位置を使って最後の出現を扱う。
使われ方：交換対の二つの実際の切断符号を同じ元位置の逆転数で比較する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：削除後の区切りは削除位置以外の将来の同色出現を持つ（BF §1.2.3）。
方針：将来位置を削除の順序単射で前後に移す。
規約：任意の語に成立する。
使われ方：削除後の区切り集合の一般計算。 -/
lemma caesura_erase_iff_witness {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (a : Fin l) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) a ↔
      ∃ b : Fin (l + 1), b ≠ i ∧ i.succAbove a < b ∧ u b = u (i.succAbove a) := by
  constructor
  · rintro ⟨b, hab, hu⟩
    exact ⟨i.succAbove b, Fin.succAbove_ne i b, Fin.strictMono_succAbove i hab, hu⟩
  · rintro ⟨b, hbi, hab, hu⟩
    obtain ⟨c, hc⟩ := Fin.exists_succAbove_eq hbi
    refine ⟨c, ?_, ?_⟩
    · apply (Fin.strictMono_succAbove i).lt_iff_lt.mp
      rwa [hc]
    · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_apply, hc] using hu

/-- 概要：区切り位置自身の削除は他の区切りを保つ（BF §1.2.3）。
方針：削除位置が唯一の将来出現だった場合は、その位置のさらに将来の出現を使う。
規約：元切断の非退化性を要求しない。
使われ方：二つとも区切りである交換位置の削除符号を比較する。 -/
lemma caesura_erase_of_caesura {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i) (a : Fin l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) a ↔ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u (i.succAbove a) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_erase_iff_witness]
  constructor
  · rintro ⟨b, _, hab, hu⟩
    exact ⟨b, hab, hu⟩
  · rintro ⟨b, hab, hu⟩
    by_cases hbi : b = i
    · subst b
      obtain ⟨c, hic, huc⟩ := hi
      exact ⟨c, ne_of_gt hic, lt_trans hab hic, huc.trans hu⟩
    · exact ⟨b, hbi, hab, hu⟩

/-- 概要：直前の同色位置が指定されていれば最終出現削除で失う区切りはその位置だけ（BF §1.2.3）。
方針：削除位置だけを将来出現に持つ区切りを、直前の同色位置へ同定する。
規約：前後二つの同色位置の間に同色がないことを要求する。
使われ方：最後の出現を削除する交換相手の活動集合を計算する。 -/
lemma caesura_erase_final {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (a i : Fin (l + 1)) (hai : a < i) (hu : u a = u i) (hi : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i)
    (hgap : ∀ b, a < b → b < i → u b ≠ u i) (b : Fin l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) b ↔ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u (i.succAbove b) ∧ i.succAbove b ≠ a := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_erase_iff_witness]
  constructor
  · rintro ⟨c, hci, hbc, huc⟩
    refine ⟨⟨c, hbc, huc⟩, ?_⟩
    intro he
    rw [he] at hbc huc
    rcases lt_or_gt_of_ne hci with hci | hic
    · exact hgap c hbc hci (huc.trans hu)
    · exact hi ⟨c, hic, huc.trans hu⟩
  · rintro ⟨⟨c, hbc, huc⟩, hba⟩
    by_cases hci : c = i
    · subst c
      have hba' : i.succAbove b < a := by
        rcases lt_or_gt_of_ne hba with hba' | hab
        · exact hba'
        · exact False.elim (hgap _ hab hbc huc.symm)
      exact ⟨a, ne_of_lt hai, hba', hu.trans huc⟩
    · exact ⟨c, hci, hbc, huc⟩

/-- 概要：同色の二位置の間に同色がなければ後の直前の出現は前の位置（BF §1.2.3）。
方針：前の出現集合の最大を、指定位置の所属と間の同色不在で比較する。
規約：それより前には何個の同色出現があってもよい。
使われ方：最終出現の削除係数の符号反転。 -/
lemma previousOccurrences_max_gap {n l : ℕ} (u : Fin l → Fin n) (a b : Fin l)
    (hab : a < b) (hu : u a = u b) (hgap : ∀ j, a < j → j < b → u j ≠ u b)
    (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u b).Nonempty) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u b).max' hp = a := by
  apply le_antisymm
  · apply Finset.max'_le
    intro j hj
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_contra hja
    exact hgap j (lt_of_not_ge hja) hj.1 hj.2
  · apply Finset.le_max'
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hab, hu⟩

/-- 概要：後の位置が最終出現なら直前同色との二削除係数は反対（BF §1.2.3）。
方針：直前の同色位置の最大公式を既存の最終出現の係数公式へ代入する。
規約：位置は物理的に隣接していなくてもよい。
使われ方：一方だけが区切りである余分削除対の係数の反対性。 -/
lemma deletionCoefficient_final_gap {n l : ℕ} (u : Fin l → Fin n) (a b : Fin l)
    (hab : a < b) (hu : u a = u b) (hb : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u b)
    (hgap : ∀ j, a < j → j < b → u j ≠ u b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u b = -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u a := by
  have hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u b).Nonempty :=
    ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, hu⟩⟩
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_final u b hb hp, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.previousOccurrences_max_gap u a b hab hu hgap hp]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
