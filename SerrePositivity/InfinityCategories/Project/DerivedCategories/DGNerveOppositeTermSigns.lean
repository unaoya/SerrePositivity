module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeSigns
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex
/-!
概要：HA 微分式の内部点削除に対する、反転の実符号式。
方針：元と反転後の左右濃度を使い、全指数の差を明示的な偶数にする。
規約：元の濃度から一点を消す。使われ方：符号付き反転の微分式の保存。
-/
@[expose] public section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 一点削除の反転符号と、元・反転後の HA 内部点符号の一致。 -/
lemma sign_delete (m l r : ℕ) (hm : 1 ≤ m) (h : m + 1 = l + r) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign m * ((l : ℤ) - 1).negOnePow =
      ((r : ℤ) - 1).negOnePow * _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (m - 1) := by
  have hmz : (m : ℤ) + 1 = (l : ℤ) + (r : ℤ) := by exact_mod_cast h
  have hs : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign m = ((m : ℤ) - 1).negOnePow * _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (m - 1) := by
    simpa only [Nat.sub_add_cancel hm, Nat.cast_sub hm, Nat.cast_one] using _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign_succ (m - 1)
  have he : ((m : ℤ) - 1 + ((l : ℤ) - 1)).negOnePow = ((r : ℤ) - 1).negOnePow := by
    apply (Int.negOnePow_eq_iff _ _).mpr
    refine ⟨(l : ℤ) - 1, ?_⟩
    omega
  rw [hs]
  calc
    _ = (((m : ℤ) - 1).negOnePow * ((l : ℤ) - 1).negOnePow) * _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign (m - 1) := by
      ac_rfl
    _ = _ := by rw [← Int.negOnePow_add, he]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
variable {n : ℕ} (I : Finset (Fin (n + 1))) (j : Fin (n + 1)) (hj : j ∈ I)
include hj in
/-- 内部点を含む右切断からその点を消すと、符号に使う厳密右切断になる。 -/
lemma strictRight_card : (I.filter (j < ·)).card + 1 = (I.filter (j ≤ ·)).card := by
  have he : (I.filter (j ≤ ·)).erase j = I.filter (j < ·) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_filter]
    constructor
    · rintro ⟨hne, hx, hjx⟩
      exact ⟨hx, lt_of_le_of_ne hjx (Ne.symm hne)⟩
    · rintro ⟨hx, hjx⟩
      exact ⟨ne_of_gt hjx, hx, hjx.le⟩
  have h := Finset.card_erase_add_one (show j ∈ I.filter (j ≤ ·) by simp [hj])
  rwa [he] at h
include hj in
/-- 左切断についての同じ実濃度式。 -/
lemma strictLeft_card : (I.filter (· < j)).card + 1 = (I.filter (· ≤ j)).card := by
  have he : (I.filter (· ≤ j)).erase j = I.filter (· < j) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_filter]
    constructor
    · rintro ⟨hne, hx, hxj⟩
      exact ⟨hx, lt_of_le_of_ne hxj hne⟩
    · rintro ⟨hx, hxj⟩
      exact ⟨ne_of_lt hxj, hx, hxj.le⟩
  have h := Finset.card_erase_add_one (show j ∈ I.filter (· ≤ j) by simp [hj])
  rwa [he] at h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
