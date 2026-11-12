module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ShuffleCutDiagonal

/-!
概要：対角に残る指定格子路の前半・後半の切断を恒等写像と照合する。
方針：水平・垂直ステップの濃度を、それぞれ初期区間との明示的な全単射で計算する。
規約：既存の awFront・awBack と格子路の left・right の値を計算する。
使われ方：HA 1.2.4、G10 の正規化 shuffle→AW の対角成分。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- 水平部分の初期 x ステップの濃度。 -/
theorem initialShuffle_prefix_card {p n x : ℕ} (h : p ≤ n) (hx : x ≤ p) :
    ((initialShuffle p n h).val.filter (fun j : Fin n => (j : ℕ) < x)).card = x := by
  let s := (initialShuffle p n h).val.filter (fun j : Fin n => (j : ℕ) < x)
  have he : s.card = (Finset.univ : Finset (Fin x)).card := by
    apply Finset.card_bij (fun (j : Fin n) (hj : j ∈ s) => (⟨j, (Finset.mem_filter.mp hj).2⟩ : Fin x))
    · intro j hj
      exact Finset.mem_univ _
    · intro j hj k hk he
      exact Fin.ext (congrArg (fun z : Fin x => z.val) he)
    · intro k hk
      let j : Fin n := ⟨k, lt_of_lt_of_le k.isLt (hx.trans h)⟩
      have hj : j ∈ s := Finset.mem_filter.mpr
        ⟨(mem_initialShuffle h j).mpr (lt_of_lt_of_le k.isLt hx), k.isLt⟩
      exact ⟨j, hj, Fin.ext rfl⟩
  simpa only [Finset.card_univ, Fintype.card_fin] using he

/-- 垂直部分の初期 x ステップの濃度。 -/
theorem initialShuffle_suffix_card {p q n x : ℕ} (h : p + q = n) (hx : x ≤ q) :
    ((initialShuffle p n (by omega)).valᶜ.filter (fun j : Fin n => (j : ℕ) < p + x)).card = x := by
  let hp : p ≤ n := by omega
  let s := (initialShuffle p n hp).valᶜ.filter (fun j : Fin n => (j : ℕ) < p + x)
  have he : s.card = (Finset.univ : Finset (Fin x)).card := by
    apply Finset.card_bij (fun (j : Fin n) (hj : j ∈ s) => (⟨j.val - p, by
      have hj₁ := (Finset.mem_filter.mp hj).1
      have hj₂ := (Finset.mem_filter.mp hj).2
      have hn := Finset.mem_compl.mp hj₁
      have hjp : p ≤ j.val := Nat.le_of_not_gt (fun ht => hn ((mem_initialShuffle hp j).mpr ht))
      omega⟩ : Fin x))
    · intro j hj
      exact Finset.mem_univ _
    · intro j hj k hk he
      have hjp : p ≤ j.val := Nat.le_of_not_gt (fun ht =>
        (Finset.mem_compl.mp (Finset.mem_filter.mp hj).1) ((mem_initialShuffle hp j).mpr ht))
      have hkp : p ≤ k.val := Nat.le_of_not_gt (fun ht =>
        (Finset.mem_compl.mp (Finset.mem_filter.mp hk).1) ((mem_initialShuffle hp k).mpr ht))
      have hv := congrArg (fun z : Fin x => z.val) he
      apply Fin.ext
      dsimp at hv
      omega
    · intro k hk
      let j : Fin n := ⟨p + k, by have := k.isLt; omega⟩
      have hj : j ∈ s := by
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_compl.mpr
          intro hm
          have := (mem_initialShuffle hp j).mp hm
          dsimp [j] at this
          omega
        · change p + k.val < p + x
          omega
      exact ⟨j, hj, Fin.ext (Nat.add_sub_cancel_left p k.val)⟩
  simpa only [Finset.card_univ, Fintype.card_fin] using he

/-- 指定格子路の前半切断は恒等。 -/
theorem initialShuffle_front (p n : ℕ) (h : p ≤ n) :
    awFront n ⟨p, Nat.lt_succ_of_le h⟩ ≫ (initialShuffle p n h).left = 𝟙 ⦋p⦌ := by
  apply SimplexCategory.Hom.ext
  ext j
  exact initialShuffle_prefix_card h (Nat.le_of_lt_succ j.isLt)

/-- 指定格子路の後半切断も恒等。 -/
theorem initialShuffle_back (p n : ℕ) (h : p ≤ n) :
    awBack n ⟨p, Nat.lt_succ_of_le h⟩ ≫
      (initialShuffle p n h).right (Nat.add_sub_of_le h) = 𝟙 ⦋n - p⦌ := by
  apply SimplexCategory.Hom.ext
  ext j
  exact initialShuffle_suffix_card (Nat.add_sub_of_le h) (Nat.le_of_lt_succ j.isLt)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
