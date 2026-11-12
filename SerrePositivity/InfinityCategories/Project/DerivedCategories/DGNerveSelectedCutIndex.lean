module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveTensorBlockDifferential
/-!
概要：選択した第一成分の添字の削除と左右分割を同定する。
方針：端点と選択点の有限集合を直接比較し、その点数を計算する。
規約：元の実 cochain と同じ有限切断集合を使う。使われ方：tensor 候補の全次元 HA の照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 同じ切断添字と元の HA 成分の比較。 -/
lemma dgNerveSelectedCutIndex_erase {n : ℕ} (S : Finset (Fin (n + 1)))
    (a b j : Fin (n + 1)) (haj : a < j) (hjb : j < b) :
    (insert a (insert b S)).erase j = insert a (insert b (S.erase j)) := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_insert]
  constructor
  · rintro ⟨hxj, rfl | rfl | hx⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨hxj, hx⟩)
  · rintro (rfl | rfl | ⟨hxj, hx⟩)
    · exact ⟨ne_of_lt haj, Or.inl rfl⟩
    · exact ⟨Ne.symm (ne_of_lt hjb), Or.inr (Or.inl rfl)⟩
    · exact ⟨hxj, Or.inr (Or.inr hx)⟩
/-- 同じ切断添字と元の HA 成分の比較。 -/
lemma dgNerveSelectedCutIndex_left {n : ℕ} (S : Finset (Fin (n + 1)))
    (a b j : Fin (n + 1)) (hj : j ∈ S) (haj : a < j) (hjb : j < b) :
    (insert a (insert b S)).filter (· ≤ j) = insert a (insert j (S.filter (· < j))) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | rfl | hx, hxj⟩
    · exact Or.inl rfl
    · exact False.elim ((not_le_of_gt hjb) hxj)
    · rcases hxj.eq_or_lt with rfl | hxlt
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨hx, hxlt⟩)
  · rintro (rfl | rfl | ⟨hx, hxlt⟩)
    · exact ⟨Or.inl rfl, haj.le⟩
    · exact ⟨Or.inr (Or.inr hj), le_rfl⟩
    · exact ⟨Or.inr (Or.inr hx), hxlt.le⟩
/-- 同じ切断添字と元の HA 成分の比較。 -/
lemma dgNerveSelectedCutIndex_right {n : ℕ} (S : Finset (Fin (n + 1)))
    (a b j : Fin (n + 1)) (hj : j ∈ S) (haj : a < j) (hjb : j < b) :
    (insert a (insert b S)).filter (j ≤ ·) = insert j (insert b (S.filter (j < ·))) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | rfl | hx, hjx⟩
    · exact False.elim ((not_le_of_gt haj) hjx)
    · exact Or.inr (Or.inl rfl)
    · rcases hjx.eq_or_lt with h | hjlt
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr ⟨hx, hjlt⟩)
  · rintro (rfl | rfl | ⟨hx, hjlt⟩)
    · exact ⟨Or.inr (Or.inr hj), le_rfl⟩
    · exact ⟨Or.inr (Or.inl rfl), hjb.le⟩
    · exact ⟨Or.inr (Or.inr hx), hjlt.le⟩
/-- 同じ切断添字と元の HA 成分の比較。 -/
lemma dgNerveSelectedCutIndex_card {n : ℕ} (S : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (hab : a < b) (hc : ∀ j ∈ S, a < j ∧ j < b) :
    (insert a (insert b S)).card = S.card + 2 := by
  have haS : a ∉ S := fun ha => (lt_irrefl a) (hc a ha).1
  have hbS : b ∉ S := fun hb => (lt_irrefl b) (hc b hb).2
  have haBS : a ∉ insert b S := by simp [ne_of_lt hab, haS]
  rw [Finset.card_insert_of_notMem haBS, Finset.card_insert_of_notMem hbS]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
