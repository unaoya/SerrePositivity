module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveCutCrossCounting
/-!
概要：同じ tensor 切断項の交差符号を挿入・削除・左右分割で比較する。
方針：有限交差の点数から整数指数と実際の符号係数の一致を証明する。
規約：同じ実切断集合の有限交差を数える。使われ方：全次元 tensor 候補の HA の符号照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 同じ有限切断の交差数から得られる符号照合。 -/
lemma dgNerveTensorCutSign_insert {n : ℕ} (I S : Finset (Fin (n + 1)))
    (a b j : Fin (n + 1)) (hS : S ⊆ (I.erase a).erase b)
    (hjI : j ∈ (I.erase a).erase b) (hjS : j ∉ S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b (insert j S) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b S +
      ((((I.erase a).erase b).filter (j < ·)).card : ℤ) - (S.card : ℤ) := by
  have hSj : insert j S ⊆ (I.erase a).erase b := Finset.insert_subset hjI hS
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutCross_eq_rank _ _ hSj, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutCross_eq_rank _ _ hS,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutRank_insert _ _ j hjS, Finset.card_insert_of_notMem hjS]
  have hc : (S.card + 1).choose 2 = S.card.choose 2 + S.card := by
    simpa only [Nat.choose_one_right, Nat.add_comm] using (Nat.choose_succ_succ' S.card 1)
  rw [hc]
  push_cast
  ring
/-- 同じ有限切断の交差数から得られる符号照合。 -/
lemma dgNerveTensorCutSign_erase {n : ℕ} (I S : Finset (Fin (n + 1)))
    (a b j : Fin (n + 1)) (hS : S ⊆ (I.erase a).erase b)
    (hjI : j ∈ (I.erase a).erase b) (hjS : j ∉ S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign (I.erase j) a b S = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b S -
      ((S.filter (· < j)).card : ℤ) := by
  let T := (I.erase a).erase b
  have he : ((I.erase j).erase a).erase b = T.erase j := by
    ext x
    simp only [T, Finset.mem_erase]
    tauto
  have hSE : S ⊆ T.erase j := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun hxj => hjS (hxj ▸ hx), hS hx⟩
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign
  rw [he, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutCross_eq_rank _ _ hSE, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutCross_eq_rank _ _ hS]
  have hcard := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutRank_erase T S j hjI
  dsimp only [T] at hcard ⊢
  omega
/-- 同じ有限切断の交差数から得られる符号照合。 -/
lemma dgNerveTensorCutSign_split {n : ℕ} (I S : Finset (Fin (n + 1)))
    (a b j : Fin (n + 1)) (hS : S ⊆ (I.erase a).erase b) (hj : j ∈ S)
    (haj : a < j) (hjb : j < b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b S =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign (I.filter (· ≤ j)) a j (S.filter (· < j)) +
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign (I.filter (j ≤ ·)) j b (S.filter (j < ·)) +
      ((S.filter (· < j)).card + 1 : ℤ) *
        (((((I.erase a).erase b).filter (j < ·)).card : ℤ) -
          ((S.filter (j < ·)).card : ℤ)) := by
  have hL : (((I.filter (· ≤ j)).erase a).erase j) =
      ((I.erase a).erase b).filter (· < j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hxj, hxa, hxI, hxle⟩
      have hxlt : x < j := lt_of_le_of_ne hxle hxj
      exact ⟨⟨ne_of_lt (lt_trans hxlt hjb), hxa, hxI⟩, hxlt⟩
    · rintro ⟨⟨_, hxa, hxI⟩, hxlt⟩
      exact ⟨ne_of_lt hxlt, hxa, hxI, le_of_lt hxlt⟩
  have hR : (((I.filter (j ≤ ·)).erase j).erase b) =
      ((I.erase a).erase b).filter (j < ·) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hxb, hxj, hxI, hjle⟩
      have hjlt : j < x := lt_of_le_of_ne hjle (Ne.symm hxj)
      exact ⟨⟨hxb, Ne.symm (ne_of_lt (lt_trans haj hjlt)), hxI⟩, hjlt⟩
    · rintro ⟨⟨hxb, _, hxI⟩, hjlt⟩
      exact ⟨hxb, Ne.symm (ne_of_lt hjlt), hxI, le_of_lt hjlt⟩
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign
  rw [hL, hR]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutCross_split _ _ j hS hj
/-- 同じ有限切断の交差数から得られる符号照合。 -/
lemma dgNerveTensorCutSign_split_exponent {n : ℕ} (I S : Finset (Fin (n + 1)))
    (a b j : Fin (n + 1)) (hS : S ⊆ (I.erase a).erase b) (hj : j ∈ S)
    (haj : a < j) (hjb : j < b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b S + ((S.filter (j < ·)).card : ℤ) + 1 =
      (((((I.erase a).erase b).filter (j < ·)).card : ℤ) + 1) +
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign (I.filter (· ≤ j)) a j (S.filter (· < j)) +
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign (I.filter (j ≤ ·)) j b (S.filter (j < ·)) +
      (-((S.filter (· < j)).card : ℤ)) *
        (2 - (((((I.erase a).erase b).filter (j < ·)).card : ℤ) + 2) +
          ((S.filter (j < ·)).card : ℤ)) := by
  rw [dgNerveTensorCutSign_split I S a b j hS hj haj hjb]
  ring
/-- 同じ有限切断の交差数から得られる符号照合。 -/
lemma dgNerveTensorCutSign_insert_coefficient {n : ℕ} (I S : Finset (Fin (n + 1)))
    (a b j : Fin (n + 1)) (hS : S ⊆ (I.erase a).erase b)
    (hjI : j ∈ (I.erase a).erase b) (hjS : j ∉ S) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b (insert j S) +
      ((S.filter (j < ·)).card : ℤ) + 1).negOnePow =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b S - (S.card : ℤ) +
      (((((I.erase a).erase b).filter (j < ·)).card : ℤ) + 1) -
      ((S.filter (j < ·)).card : ℤ)).negOnePow := by
  rw [Int.negOnePow_eq_iff, dgNerveTensorCutSign_insert I S a b j hS hjI hjS]
  exact ⟨((S.filter (j < ·)).card : ℤ), by ring⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
