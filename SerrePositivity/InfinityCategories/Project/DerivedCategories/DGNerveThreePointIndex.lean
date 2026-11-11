module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index
/-!
概要：三点集合を指定した両端と唯一の中間点で表示する。
方針：最小・最大を消した集合の濃度一から、中間点と厳密な順序を回収する。
規約：任意の線形順序で成り立つ。使われ方：候補 cochain の低次 HA から実単体への昇格。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 三点集合は、指定した最小・最大とその間の一意な点からなる。 -/
lemma dgNerveIndex_eq_triple_of_card_three {α : Type u} [LinearOrder α]
    (I : Finset α) (a c : α) (hI : I.card = 3)
    (ha : IsLeast (I : Set α) a) (hc : IsGreatest (I : Set α) c) :
    ∃ b, I = {a, b, c} ∧ a < b ∧ b < c := by
  classical
  have hac : a < c := by
    have h := I.min'_lt_max'_of_card (by omega)
    simpa only [← ha.unique (I.isLeast_min' ⟨a, ha.1⟩),
      ← hc.unique (I.isGreatest_max' ⟨a, ha.1⟩)] using h
  have hcE : c ∈ I.erase a := Finset.mem_erase.mpr ⟨ne_of_gt hac, hc.1⟩
  have hcard : ((I.erase a).erase c).card = 1 := by
    rw [Finset.card_erase_of_mem hcE, Finset.card_erase_of_mem ha.1, hI]
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcard
  have hbE : b ∈ (I.erase a).erase c := by rw [hb]; simp
  obtain ⟨hbc, hbE⟩ := Finset.mem_erase.mp hbE
  obtain ⟨hba, hbI⟩ := Finset.mem_erase.mp hbE
  have hab : a < b := lt_of_le_of_ne (ha.2 hbI) hba.symm
  have hbc' : b < c := lt_of_le_of_ne (hc.2 hbI) hbc
  refine ⟨b, ?_, hab, hbc'⟩
  have hi : insert a (insert c {b}) = I := by
    rw [← hb, Finset.insert_erase hcE, Finset.insert_erase ha.1]
  rw [← hi]
  ext j
  simp [or_comm]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
