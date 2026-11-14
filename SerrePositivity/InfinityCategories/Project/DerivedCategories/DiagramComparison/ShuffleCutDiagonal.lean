module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ShuffleCutNormalization

/-!
概要：正規化 shuffle→AW の対角成分に残る格子路とその符号を同定する。
方針：前半の切断が単射なら自己単射は恒等。終点の値と濃度から水平ステップを決める。
規約：既存 ShuffleIndex と inversions の定義を保持する。
使われ方：HA 1.2.4、G10 の指定二比較の合成の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- 水平ステップを最初に並べた指定格子路。 -/
def initialShuffle (p n : ℕ) (h : p ≤ n) : ShuffleIndex p n :=
  ⟨Finset.univ.map ⟨fun j : Fin p => ⟨j, lt_of_lt_of_le j.isLt h⟩,
    fun _ _ he => Fin.ext (congrArg (fun j : Fin n => j.val) he)⟩, by simp⟩

/-- 指定格子路の水平ステップは p より前のステップにちょうど一致。 -/
@[simp]
theorem mem_initialShuffle {p n : ℕ} (h : p ≤ n) (j : Fin n) :
    j ∈ (initialShuffle p n h).val ↔ (j : ℕ) < p := by
  constructor
  · intro hj
    obtain ⟨k, _, hk⟩ := Finset.mem_map.mp hj
    have hv := congrArg Fin.val hk
    exact hv ▸ k.isLt
  · intro hj
    apply Finset.mem_map.mpr
    exact ⟨⟨j, hj⟩, Finset.mem_univ _, Fin.ext rfl⟩

/-- 対角の前半が単射なら、水平ステップは全て切断点より前にある。 -/
theorem shuffle_mem_lt_of_front_mono {p n : ℕ} (h : p ≤ n)
    (s : ShuffleIndex p n) [Mono (awFront n ⟨p, Nat.lt_succ_of_le h⟩ ≫ s.left)] :
    ∀ j ∈ s.val, (j : ℕ) < p := by
  have he := SimplexCategory.eq_id_of_mono (awFront n ⟨p, Nat.lt_succ_of_le h⟩ ≫ s.left)
  have hv := congrArg (fun f : SimplexCategory.mk p ⟶ SimplexCategory.mk p =>
    (f.toOrderHom ⟨p, Nat.lt_succ_self p⟩ : ℕ)) he
  change (s.val.filter (fun j : Fin n => (j : ℕ) < p)).card = p at hv
  exact Finset.card_filter_eq_iff.mp (hv.trans s.property.symm)

/-- 対角の前半が非退化となる格子路は指定した一つだけ。 -/
theorem shuffle_eq_initial_of_front_mono {p n : ℕ} (h : p ≤ n)
    (s : ShuffleIndex p n) [Mono (awFront n ⟨p, Nat.lt_succ_of_le h⟩ ≫ s.left)] :
    s = initialShuffle p n h := by
  apply Subtype.ext
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    exact (mem_initialShuffle h j).mpr (shuffle_mem_lt_of_front_mono h s j hj)
  · rw [s.property, (initialShuffle p n h).property]

/-- 指定格子路には逆転がない。 -/
@[simp]
theorem initialShuffle_inversions (p n : ℕ) (h : p ≤ n) :
    (initialShuffle p n h).inversions = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  obtain ⟨hk, hkj⟩ := Finset.mem_filter.mp hk
  have hjp := (mem_initialShuffle h j).mp hj
  have hkp : (k : ℕ) < p := lt_trans hkj hjp
  exact (Finset.mem_compl.mp hk) ((mem_initialShuffle h k).mpr hkp)

/-- 残る格子路の shuffle 符号は +1。 -/
@[simp]
theorem initialShuffle_sign (p n : ℕ) (h : p ≤ n) :
    (-1 : ℤ) ^ (initialShuffle p n h).inversions = 1 := by
  rw [initialShuffle_inversions, pow_zero]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
