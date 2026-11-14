module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorCutTerm
public import Mathlib.Data.Nat.Choose.Basic
/-!
概要：切断点の挿入・削除・左右分割による有限交差数の変化を計算する。
方針：交差を互いに素な有限集合へ分解し、その点数を足し合わせる。
規約：同じ実切断集合の有限交差を数える。使われ方：全次元 tensor 候補の HA の符号照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 同じ有限切断の交差数から得られる符号照合。 -/
lemma dgNerveCutCross_eq_rank {α : Type u} [LinearOrder α] (T S : Finset α) (hS : S ⊆ T) :
    (((S.product (T.filter (fun y => y ∉ S))).filter (fun p => p.1 < p.2)).card : ℤ) =
      (((S.product T).filter (fun p => p.1 < p.2)).card : ℤ) - (S.card.choose 2 : ℤ) := by
  classical
  let U := (S.product T).filter (fun p => p.1 < p.2)
  let V := (S.product S).filter (fun p => p.1 < p.2)
  let W := (S.product (T.filter (fun y => y ∉ S))).filter (fun p => p.1 < p.2)
  have hU : U = V ∪ W := by
    ext ⟨x, y⟩
    simp only [U, V, W, Finset.mem_filter, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_union]
    constructor
    · rintro ⟨⟨hx, hy⟩, hxy⟩
      by_cases hyS : y ∈ S
      · exact Or.inl ⟨⟨hx, hyS⟩, hxy⟩
      · exact Or.inr ⟨⟨hx, hy, hyS⟩, hxy⟩
    · rintro (⟨⟨hx, hy⟩, hxy⟩ | ⟨⟨hx, hy, _⟩, hxy⟩)
      · exact ⟨⟨hx, hS hy⟩, hxy⟩
      · exact ⟨⟨hx, hy⟩, hxy⟩
  have hd : Disjoint V W := by
    apply Finset.disjoint_left.mpr
    intro p hpV hpW
    have hyS := (Finset.mem_product.mp (Finset.mem_filter.mp hpV).1).2
    have hyNot := (Finset.mem_filter.mp
      (Finset.mem_product.mp (Finset.mem_filter.mp hpW).1).2).2
    exact hyNot hyS
  have hcard := Finset.card_union_of_disjoint hd
  rw [← hU] at hcard
  have hV : V.card = S.card.choose 2 := Finset.card_product_filter_lt (s := S)
  change (W.card : ℤ) = (U.card : ℤ) - (S.card.choose 2 : ℤ)
  omega
/-- 同じ有限切断の交差数から得られる符号照合。 -/
lemma dgNerveCutRank_insert {α : Type u} [LinearOrder α] (T S : Finset α) (j : α)
    (hj : j ∉ S) :
    (((insert j S).product T).filter (fun p => p.1 < p.2)).card =
      ((S.product T).filter (fun p => p.1 < p.2)).card + (T.filter (j < ·)).card := by
  classical
  let U := (S.product T).filter (fun p => p.1 < p.2)
  let V := (({j} : Finset α).product T).filter (fun p => p.1 < p.2)
  have hv : V = ({j} : Finset α).product (T.filter (j < ·)) := by
    ext ⟨x, y⟩
    simp only [V, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨rfl, hy⟩, hxy⟩
      exact ⟨rfl, hy, hxy⟩
    · rintro ⟨rfl, hy, hxy⟩
      exact ⟨⟨rfl, hy⟩, hxy⟩
  have hu : ((insert j S).product T).filter (fun p => p.1 < p.2) = U ∪ V := by
    ext ⟨x, y⟩
    simp only [U, V, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
      Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_union]
    aesop
  have hd : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro p hpU hpV
    have hx := (Finset.mem_product.mp (Finset.mem_filter.mp hpU).1).1
    have hxj := Finset.mem_singleton.mp (Finset.mem_product.mp (Finset.mem_filter.mp hpV).1).1
    exact hj (hxj ▸ hx)
  rw [hu, Finset.card_union_of_disjoint hd, hv]
  simp [U]
/-- 同じ有限切断の交差数から得られる符号照合。 -/
lemma dgNerveCutRank_erase {α : Type u} [LinearOrder α] (T S : Finset α) (j : α)
    (hj : j ∈ T) :
    ((S.product T).filter (fun p => p.1 < p.2)).card =
      ((S.product (T.erase j)).filter (fun p => p.1 < p.2)).card + (S.filter (· < j)).card := by
  classical
  let U := (S.product T).filter (fun p => p.1 < p.2)
  let V := (S.product (T.erase j)).filter (fun p => p.1 < p.2)
  let W := (S.filter (· < j)).product ({j} : Finset α)
  have hu : U = V ∪ W := by
    ext ⟨x, y⟩
    simp only [U, V, W, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
      Finset.mem_erase, Finset.mem_singleton, Finset.mem_union]
    constructor
    · rintro ⟨⟨hx, hy⟩, hxy⟩
      by_cases hyj : y = j
      · subst y
        exact Or.inr ⟨⟨hx, hxy⟩, rfl⟩
      · exact Or.inl ⟨⟨hx, hyj, hy⟩, hxy⟩
    · rintro (⟨⟨hx, _, hy⟩, hxy⟩ | ⟨⟨hx, hxy⟩, rfl⟩)
      · exact ⟨⟨hx, hy⟩, hxy⟩
      · exact ⟨⟨hx, hj⟩, hxy⟩
  have hd : Disjoint V W := by
    apply Finset.disjoint_left.mpr
    intro p hpV hpW
    have hyj := (Finset.mem_erase.mp (Finset.mem_product.mp (Finset.mem_filter.mp hpV).1).2).1
    have hy : p.2 = j := Finset.mem_singleton.mp (Finset.mem_product.mp hpW).2
    exact hyj hy
  change U.card = V.card + (S.filter (· < j)).card
  rw [hu, Finset.card_union_of_disjoint hd]
  simp [W]
/-- 同じ有限切断の交差数から得られる符号照合。 -/
lemma dgNerveCutCross_split {α : Type u} [LinearOrder α] (T S : Finset α)
    (j : α) (hS : S ⊆ T) (hj : j ∈ S) :
    (((S.product (T.filter (fun y => y ∉ S))).filter (fun p => p.1 < p.2)).card : ℤ) =
      ((((S.filter (· < j)).product
        ((T.filter (· < j)).filter (fun y => y ∉ S.filter (· < j)))).filter
          (fun p => p.1 < p.2)).card : ℤ) +
      ((((S.filter (j < ·)).product
        ((T.filter (j < ·)).filter (fun y => y ∉ S.filter (j < ·)))).filter
          (fun p => p.1 < p.2)).card : ℤ) +
      ((S.filter (· < j)).card + 1 : ℤ) *
        ((T.filter (j < ·)).card - (S.filter (j < ·)).card : ℤ) := by
  classical
  let L := S.filter (· < j)
  let M := S.filter (j < ·)
  let TL := T.filter (· < j)
  let TR := T.filter (j < ·)
  let U := (S.product (T.filter (fun y => y ∉ S))).filter (fun p => p.1 < p.2)
  let V := (L.product (TL.filter (fun y => y ∉ L))).filter (fun p => p.1 < p.2)
  let W := (M.product (TR.filter (fun y => y ∉ M))).filter (fun p => p.1 < p.2)
  let Z := (insert j L).product (TR.filter (fun y => y ∉ M))
  have hu : U = (V ∪ W) ∪ Z := by
    ext ⟨x, y⟩
    simp only [U, V, W, Z, L, M, TL, TR, Finset.mem_filter,
      Finset.product_eq_sprod, Finset.mem_product, Finset.mem_insert, Finset.mem_union]
    constructor
    · rintro ⟨⟨hx, hy, hyS⟩, hxy⟩
      by_cases hyl : y < j
      · exact Or.inl (Or.inl ⟨⟨⟨hx, lt_trans hxy hyl⟩, ⟨hy, hyl⟩,
          fun hyL => hyS hyL.1⟩, hxy⟩)
      · have hjy : j < y := lt_of_le_of_ne (le_of_not_gt hyl) (by
          intro h; exact hyS (h ▸ hj))
        by_cases hxj : j < x
        · exact Or.inl (Or.inr ⟨⟨⟨hx, hxj⟩, ⟨hy, hjy⟩,
            fun hyM => hyS hyM.1⟩, hxy⟩)
        · exact Or.inr ⟨(le_of_not_gt hxj).eq_or_lt.imp_left id |>.imp_right
            (fun h => ⟨hx, h⟩), ⟨hy, hjy⟩, fun hyM => hyS hyM.1⟩
    · rintro ((⟨⟨⟨hx, hxj⟩, ⟨hy, hyj⟩, hyL⟩, hxy⟩ |
          ⟨⟨⟨hx, hjx⟩, ⟨hy, hjy⟩, hyM⟩, hxy⟩) |
          ⟨hx, ⟨hy, hjy⟩, hyM⟩)
      · exact ⟨⟨hx, hy, fun hyS => hyL ⟨hyS, hyj⟩⟩, hxy⟩
      · exact ⟨⟨hx, hy, fun hyS => hyM ⟨hyS, hjy⟩⟩, hxy⟩
      · rcases hx with rfl | ⟨hx, hxj⟩
        · exact ⟨⟨hj, hy, fun hyS => hyM ⟨hyS, hjy⟩⟩, hjy⟩
        · exact ⟨⟨hx, hy, fun hyS => hyM ⟨hyS, hjy⟩⟩, lt_trans hxj hjy⟩
  have hvw : Disjoint V W := by
    apply Finset.disjoint_left.mpr
    intro p hpV hpW
    have hV := (Finset.mem_filter.mp
      (Finset.mem_product.mp (Finset.mem_filter.mp hpV).1).1).2
    have hW := (Finset.mem_filter.mp
      (Finset.mem_product.mp (Finset.mem_filter.mp hpW).1).1).2
    exact (lt_asymm hV hW)
  have hvz : Disjoint V Z := by
    apply Finset.disjoint_left.mpr
    intro p hpV hpZ
    have hV := (Finset.mem_filter.mp
      (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp hpV).1).2).1).2
    have hZ := (Finset.mem_filter.mp
      (Finset.mem_filter.mp (Finset.mem_product.mp hpZ).2).1).2
    exact lt_asymm hV hZ
  have hwz : Disjoint W Z := by
    apply Finset.disjoint_left.mpr
    intro p hpW hpZ
    have hW := (Finset.mem_filter.mp
      (Finset.mem_product.mp (Finset.mem_filter.mp hpW).1).1).2
    rcases Finset.mem_insert.mp (Finset.mem_product.mp hpZ).1 with h | h
    · exact (ne_of_lt hW) h.symm
    · exact lt_asymm (Finset.mem_filter.mp h).2 hW
  have hjL : j ∉ L := by simp [L]
  have hMT : M ⊆ TR := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hS (Finset.mem_filter.mp hx).1,
      (Finset.mem_filter.mp hx).2⟩
  have ht : TR.filter (fun y => y ∉ M) = TR \ M := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_sdiff]
  have hcard : U.card = V.card + W.card +
      (L.card + 1) * (TR.card - M.card) := by
    rw [hu, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hvz, hwz⟩),
      Finset.card_union_of_disjoint hvw]
    dsimp only [Z]
    rw [Finset.product_eq_sprod, Finset.card_product, Finset.card_insert_of_notMem hjL,
      ht, Finset.card_sdiff_of_subset hMT]
  change (U.card : ℤ) = (V.card : ℤ) + (W.card : ℤ) +
    ((L.card : ℤ) + 1) * ((TR.card : ℤ) - (M.card : ℤ))
  rw [hcard]
  push_cast [Nat.cast_sub (Finset.card_le_card hMT)]
  ring
end SerrePositivity.InfinityCategories.Project.DerivedCategories
