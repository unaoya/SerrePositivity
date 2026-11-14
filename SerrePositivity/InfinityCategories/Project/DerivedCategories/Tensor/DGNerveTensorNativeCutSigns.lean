module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorCutSigns
/-!
概要：切断符号の比較を元の HA の実際の添字数へ接続する。
方針：元の端点を除いた有限集合の点数から、合成・挿入・削除の係数を照合する。
規約：元の実 cochain と同じ有限切断集合を使う。使われ方：tensor 候補の全次元 HA の照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 同じ切断添字と元の HA 成分の比較。 -/
lemma dgNerveSelectedCutIndex_right_card {n : ℕ} (S : Finset (Fin (n + 1)))
    (a b j : Fin (n + 1)) (haj : a < j) (hjb : j < b) (hbS : b ∉ S) :
    (((insert a (insert b S)).filter (j < ·)).card : ℤ) =
      ((S.filter (j < ·)).card : ℤ) + 1 := by
  have he : (insert a (insert b S)).filter (j < ·) = insert b (S.filter (j < ·)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | rfl | hx, hjx⟩
      · exact False.elim (lt_asymm haj hjx)
      · exact Or.inl rfl
      · exact Or.inr ⟨hx, hjx⟩
    · rintro (rfl | ⟨hx, hjx⟩)
      · exact ⟨Or.inr (Or.inl rfl), hjb⟩
      · exact ⟨Or.inr (Or.inr hx), hjx⟩
  have hn : b ∉ S.filter (j < ·) := fun h => hbS (Finset.mem_filter.mp h).1
  rw [he, Finset.card_insert_of_notMem hn]
  push_cast
  rfl
/-- 同じ切断添字と元の HA 成分の比較。 -/
lemma dgNerveAmbientCutIndex_right_card {n : ℕ} (I : Finset (Fin (n + 1)))
    (a b j : Fin (n + 1)) (hb : b ∈ I) (haj : a < j) (hjb : j < b) :
    ((I.filter (j < ·)).card : ℤ) =
      (((((I.erase a).erase b).filter (j < ·)).card : ℤ) + 1) := by
  have he : I.filter (j < ·) = insert b (((I.erase a).erase b).filter (j < ·)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hx, hjx⟩
      by_cases hxb : x = b
      · exact Or.inl hxb
      · exact Or.inr ⟨⟨hxb, Ne.symm (ne_of_lt (lt_trans haj hjx)), hx⟩, hjx⟩
    · rintro (rfl | ⟨⟨_, _, hx⟩, hjx⟩)
      · exact ⟨hb, hjb⟩
      · exact ⟨hx, hjx⟩
  have hn : b ∉ (((I.erase a).erase b).filter (j < ·)) := by simp
  rw [he, Finset.card_insert_of_notMem hn]
  push_cast
  rfl
/-- 同じ切断添字と元の HA 成分の比較。 -/
lemma dgNerveAmbientCutIndex_right_closed_card {n : ℕ} (I : Finset (Fin (n + 1)))
    (a b j : Fin (n + 1)) (hj : j ∈ I) (hb : b ∈ I) (haj : a < j) (hjb : j < b) :
    ((I.filter (j ≤ ·)).card : ℤ) =
      (((((I.erase a).erase b).filter (j < ·)).card : ℤ) + 2) := by
  have he : I.filter (j ≤ ·) = insert j (I.filter (j < ·)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hjx⟩
      rcases hjx.eq_or_lt with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨hx, h⟩
    · rintro (rfl | ⟨hx, hjx⟩)
      · exact ⟨hj, le_rfl⟩
      · exact ⟨hx, hjx.le⟩
  have hn : j ∉ I.filter (j < ·) := by simp
  rw [he, Finset.card_insert_of_notMem hn, Nat.cast_add, Nat.cast_one,
    dgNerveAmbientCutIndex_right_card I a b j hb haj hjb]
  ring
/-- 同じ切断添字と元の HA 成分の比較。 -/
lemma dgNerveTensorCutSign_native_split_exponent {n : ℕ} (I S : Finset (Fin (n + 1)))
    (a b j : Fin (n + 1)) (hS : S ⊆ (I.erase a).erase b) (hj : j ∈ S)
    (hb : b ∈ I) (haj : a < j) (hjb : j < b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b S +
      (((insert a (insert b S)).filter (j < ·)).card : ℤ) =
      ((I.filter (j < ·)).card : ℤ) +
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign (I.filter (· ≤ j)) a j (S.filter (· < j)) +
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign (I.filter (j ≤ ·)) j b (S.filter (j < ·)) +
      (-((S.filter (· < j)).card : ℤ)) *
        (2 - ((I.filter (j ≤ ·)).card : ℤ) + ((S.filter (j < ·)).card : ℤ)) := by
  have hbS : b ∉ S := fun h => (Finset.mem_erase.mp (hS h)).1 rfl
  have hjI : j ∈ I := (Finset.mem_erase.mp (Finset.mem_erase.mp (hS hj)).2).2
  rw [dgNerveSelectedCutIndex_right_card S a b j haj hjb hbS,
    dgNerveAmbientCutIndex_right_card I a b j hb haj hjb,
    dgNerveAmbientCutIndex_right_closed_card I a b j hjI hb haj hjb]
  simpa only [add_assoc] using _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign_split_exponent I S a b j hS hj haj hjb
/-- 同じ切断添字と元の HA 成分の比較。 -/
lemma dgNerveTensorCutSign_native_insert_coefficient {n : ℕ}
    (I S : Finset (Fin (n + 1))) (a b j : Fin (n + 1))
    (hS : S ⊆ (I.erase a).erase b) (hjI : j ∈ (I.erase a).erase b)
    (hjS : j ∉ S) (hb : b ∈ I) (haj : a < j) (hjb : j < b) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b (insert j S) +
      (((insert a (insert b (insert j S))).filter (j < ·)).card : ℤ)).negOnePow =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b S - (S.card : ℤ) +
      ((I.filter (j < ·)).card : ℤ) - ((S.filter (j < ·)).card : ℤ)).negOnePow := by
  have hbS : b ∉ insert j S := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨Ne.symm (ne_of_lt hjb), fun h => (Finset.mem_erase.mp (hS h)).1 rfl⟩
  have hfil : (insert j S).filter (j < ·) = S.filter (j < ·) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hx, hjx⟩
      · exact False.elim (lt_irrefl _ hjx)
      · exact ⟨hx, hjx⟩
    · rintro ⟨hx, hjx⟩
      exact ⟨Or.inr hx, hjx⟩
  rw [dgNerveSelectedCutIndex_right_card (insert j S) a b j haj hjb hbS, hfil,
    dgNerveAmbientCutIndex_right_card I a b j hb haj hjb]
  simpa only [add_assoc] using _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign_insert_coefficient I S a b j hS hjI hjS
/-- 同じ切断添字と元の HA 成分の比較。 -/
lemma dgNerveCutCard_away {n : ℕ} (S : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) (hj : j ∉ S) :
    S.card = (S.filter (· < j)).card + (S.filter (j < ·)).card := by
  have he : S = (S.filter (· < j)) ∪ (S.filter (j < ·)) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      have hxj : x ≠ j := by
        intro h
        exact hj (h ▸ hx)
      rcases lt_or_gt_of_ne hxj with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hd : Disjoint (S.filter (· < j)) (S.filter (j < ·)) := by
    apply Finset.disjoint_left.mpr
    intro x hxL hxR
    exact lt_asymm (Finset.mem_filter.mp hxL).2 (Finset.mem_filter.mp hxR).2
  conv_lhs => rw [he]
  exact Finset.card_union_of_disjoint hd
/-- 同じ切断添字と元の HA 成分の比較。 -/
lemma dgNerveTensorCutSign_native_erase_coefficient {n : ℕ}
    (I S : Finset (Fin (n + 1))) (a b j : Fin (n + 1))
    (hS : S ⊆ (I.erase a).erase b) (hjI : j ∈ (I.erase a).erase b) (hjS : j ∉ S) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b S - (S.card : ℤ) +
      ((I.filter (j < ·)).card : ℤ) - ((S.filter (j < ·)).card : ℤ)).negOnePow =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign (I.erase j) a b S +
      ((I.filter (j < ·)).card : ℤ)).negOnePow := by
  rw [Int.negOnePow_eq_iff, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign_erase I S a b j hS hjI hjS,
    dgNerveCutCard_away S j hjS, Nat.cast_add]
  exact ⟨-((S.filter (j < ·)).card : ℤ), by ring⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
