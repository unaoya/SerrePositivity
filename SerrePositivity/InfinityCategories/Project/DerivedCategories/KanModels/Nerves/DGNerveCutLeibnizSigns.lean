module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveCutSplit
/-!
概要：先頭切断点の左右で、Leibniz 境界と全切断和の符号を比較する。
方針：元の右側添字を区間で分けて数え、整数指数の偶数差を証明する。
規約：同じ実 cochain を使う。使われ方：第二因子の全 HA 展開と tensor 候補の相殺。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

/-- 元の実切断成分と符号付き境界の照合。 -/
lemma dgNerveCutRightCard_split_at {n : ℕ} (I : Finset (Fin (n + 1)))
    (i j : Fin (n + 1)) (hi : i ∈ I) (hji : j < i) :
    ((I.filter (· ≤ i)).filter (j < ·)).card + (I.filter (i ≤ ·)).card =
      (I.filter (j < ·)).card + 1 := by
  have hL : ((I.filter (j < ·)).filter (· ≤ i)) =
      (I.filter (· ≤ i)).filter (j < ·) := by
    ext x
    simp only [Finset.mem_filter]
    tauto
  have hR : ((I.filter (j < ·)).filter (i ≤ ·)) = I.filter (i ≤ ·) := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩,
      fun h => ⟨⟨h.1, lt_of_lt_of_le hji h.2⟩, h.2⟩⟩
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card (Finset.mem_filter.mpr ⟨hi, hji⟩)
  rw [hL, hR] at h
  exact h
/-- 元の実切断成分と符号付き境界の照合。 -/
lemma dgNerveCutLeibniz_sign_left {n : ℕ} (I U : Finset (Fin (n + 1)))
    (i j : Fin (n + 1)) (hi : i ∈ I) (hji : j < i) (hU : ∀ x ∈ U, i < x) :
    (2 - ((I.filter (i ≤ ·)).card : ℤ) + (U.card : ℤ) +
      (((I.filter (· ≤ i)).filter (j < ·)).card : ℤ)).negOnePow =
    (((I.filter (j < ·)).card : ℤ) - (((insert i U).filter (j < ·)).card : ℤ)).negOnePow := by
  have hiU : i ∉ U := fun hx => lt_irrefl i (hU i hx)
  have hf : (insert i U).filter (j < ·) = insert i U := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hji
    · exact lt_trans hji (hU x hx)
  have hcard := dgNerveCutRightCard_split_at I i j hi hji
  rw [hf, Finset.card_insert_of_notMem hiU, Nat.cast_add, Nat.cast_one,
    Int.negOnePow_eq_iff]
  refine ⟨2 - ((I.filter (i ≤ ·)).card : ℤ) + (U.card : ℤ), ?_⟩
  omega
/-- 元の実切断成分と符号付き境界の照合。 -/
lemma dgNerveCutLeibniz_sign_right {n : ℕ} (I U : Finset (Fin (n + 1)))
    (i j : Fin (n + 1)) (hij : i < j) :
    ((((I.filter (i ≤ ·)).filter (j < ·)).card : ℤ) -
      ((U.filter (j < ·)).card : ℤ)).negOnePow =
    (((I.filter (j < ·)).card : ℤ) - (((insert i U).filter (j < ·)).card : ℤ)).negOnePow := by
  have hI : (I.filter (i ≤ ·)).filter (j < ·) = I.filter (j < ·) := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩,
      fun h => ⟨⟨h.1, (lt_trans hij h.2).le⟩, h.2⟩⟩
  have hU : (insert i U).filter (j < ·) = U.filter (j < ·) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hx, hjx⟩
      · exact False.elim (lt_asymm hij hjx)
      · exact ⟨hx, hjx⟩
    · rintro ⟨hx, hjx⟩
      exact ⟨Or.inr hx, hjx⟩
  rw [hI, hU]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
