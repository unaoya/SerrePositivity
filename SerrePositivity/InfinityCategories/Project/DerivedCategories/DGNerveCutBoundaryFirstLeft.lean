module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutProductFirstErase
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutProductFirstInsert
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutBoundarySum
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutLeibnizSigns
/-!
概要：先頭切断点より左の実境界項を、元の第一ブロックの HA 項へ同定する。
方針：先頭切断の実 cochain 比較と零拡張した有限和、切断集合への強帰納法を使う。
規約：全次元の同じ実成分を保つ。使われ方：tensor 候補の全 HA の有限和の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped BigOperators
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 元の実切断合成の境界項と符号付き全和の照合。 -/
lemma dgNerveCutBoundaryTerm_first_left {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b i j : Fin (n + 1)) (U : Finset (Fin (n + 1)))
    (k p q : ℤ) (hk : k = 2 - (I.card : ℤ) + ((insert i U).card : ℤ))
    (hp : p = 2 - ((I.filter (· ≤ i)).card : ℤ))
    (hq : q = 2 - ((I.filter (i ≤ ·)).card : ℤ) + (U.card : ℤ))
    (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ x ∈ insert i U, x ∈ I ∧ a < x ∧ x < b) (hmin : ∀ x ∈ U, i < x)
    (hj : j ∈ I) (haj : a < j) (hji : j < i) (hjb : j < b) (hjU : j ∉ U)
    (hP : 2 ≤ (I.filter (· ≤ i)).card)
    (haP : IsLeast ((I.filter (· ≤ i)) : Set (Fin (n + 1))) a)
    (hiP : IsGreatest ((I.filter (· ≤ i)) : Set (Fin (n + 1))) i)
    (hQ : 2 ≤ (I.filter (i ≤ ·)).card)
    (hiQ : IsLeast ((I.filter (i ≤ ·)) : Set (Fin (n + 1))) i)
    (hbQ : IsGreatest ((I.filter (i ≤ ·)) : Set (Fin (n + 1))) b)
    (hcU : ∀ x ∈ U, x ∈ I.filter (i ≤ ·) ∧ i < x ∧ x < b)
    (hcomp : (p + 1) + q = k + 1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundaryTerm R D s I a b (insert i U) j k hk ha hb hc hj haj hjb
      (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_lt hji, hjU⟩) =
      q.negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s (I.filter (i ≤ ·)) i b U q hq hQ hiQ hbQ hcU)
        (s.term (I.filter (· ≤ i)) a i p hP
          (haP.unique (Finset.isLeast_min' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP)))
          (hiP.unique (Finset.isGreatest_max' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP))) hp j
          (Finset.mem_filter.mpr ⟨hj, hji.le⟩) haj hji) hcomp := by
  have hjS : j ∉ insert i U := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨ne_of_lt hji, hjU⟩
  have hjP : j ∈ I.filter (· ≤ i) := Finset.mem_filter.mpr ⟨hj, hji.le⟩
  have hE : 2 ≤ (I.erase j).card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two ha.1 hb.1 haj hjb
  have haE : IsLeast ((I.erase j) : Set (Fin (n + 1))) a :=
    ⟨Finset.mem_erase.mpr ⟨ne_of_lt haj, ha.1⟩,
      fun _ hx => ha.2 (Finset.mem_erase.mp hx).2⟩
  have hbE : IsGreatest ((I.erase j) : Set (Fin (n + 1))) b :=
    ⟨Finset.mem_erase.mpr ⟨Ne.symm (ne_of_lt hjb), hb.1⟩,
      fun _ hx => hb.2 (Finset.mem_erase.mp hx).2⟩
  have hcE : ∀ x ∈ insert i U, x ∈ I.erase j ∧ a < x ∧ x < b := by
    intro x hx
    exact ⟨Finset.mem_erase.mpr ⟨fun hxj => hjS (hxj ▸ hx), (hc x hx).1⟩, (hc x hx).2⟩
  have hPE : 2 ≤ ((I.filter (· ≤ i)).erase j).card :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two haP.1 hiP.1 haj hji
  have haPE : IsLeast (((I.filter (· ≤ i)).erase j) : Set (Fin (n + 1))) a :=
    ⟨Finset.mem_erase.mpr ⟨ne_of_lt haj, haP.1⟩,
      fun _ hx => haP.2 (Finset.mem_erase.mp hx).2⟩
  have hiPE : IsGreatest (((I.filter (· ≤ i)).erase j) : Set (Fin (n + 1))) i :=
    ⟨Finset.mem_erase.mpr ⟨Ne.symm (ne_of_lt hji), hiP.1⟩,
      fun _ hx => hiP.2 (Finset.mem_erase.mp hx).2⟩
  have hcA : ∀ x ∈ insert j (insert i U), x ∈ I ∧ a < x ∧ x < b := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨hj, haj, hjb⟩
    · exact hc x hx
  have hcJ : ∀ x ∈ ({j} : Finset (Fin (n + 1))),
      x ∈ I.filter (· ≤ i) ∧ a < x ∧ x < i := by
    intro x hx
    have hxj := Finset.mem_singleton.mp hx
    subst x
    exact ⟨hjP, haj, hji⟩
  have hkE : k + 1 = 2 - ((I.erase j).card : ℤ) + ((insert i U).card : ℤ) := by
    have hcard := Finset.card_erase_add_one hj
    omega
  have hpE : p + 1 = 2 - (((I.filter (· ≤ i)).erase j).card : ℤ) := by
    have hcard := Finset.card_erase_add_one hjP
    omega
  have hkA : k + 1 = 2 - (I.card : ℤ) + ((insert j (insert i U)).card : ℤ) := by
    rw [Finset.card_insert_of_notMem hjS]
    push_cast
    omega
  have hpA : p + 1 = 2 - ((I.filter (· ≤ i)).card : ℤ) +
      (({j} : Finset (Fin (n + 1))).card : ℤ) := by
    simp only [Finset.card_singleton, Nat.cast_one, hp]
  let rest := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s (I.filter (i ≤ ·)) i b U q hq hQ hiQ hbQ hcU
  let deletedP := s.hom ((I.filter (· ≤ i)).erase j) a i (p + 1) hPE
    (haPE.unique (Finset.isLeast_min' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hPE)))
    (hiPE.unique (Finset.isGreatest_max' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hPE))) hpE
  let addedP := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s (I.filter (· ≤ i)) a i {j}
    (p + 1) hpA hP haP hiP hcJ
  let deleted := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s (I.erase j) a b (insert i U)
    (k + 1) hkE hE haE hbE hcE
  have hIfull : 2 ≤ I.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.two_le_card ha.1 hb.1
    (ne_of_lt (lt_trans haj hjb))
  let added := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s I a b (insert j (insert i U))
    (k + 1) hkA hIfull ha hb hcA
  have hd : deleted = compose R rest deletedP hcomp :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree_erase_before_first R D s I a b i j U hji (k + 1) (p + 1) q
      hkE hpE hq hE haE hbE hcE hmin hPE haPE hiPE hQ hiQ hbQ hcU hcomp
  have hA : added = compose R rest addedP hcomp :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree_insert_before_first R D s I a b i j U hji (k + 1) (p + 1) q
      hkA hpA hq hIfull ha hb hcA hmin hP haP hiP hQ hiQ hbQ hcJ hcU hcomp
  have hterm : s.term (I.filter (· ≤ i)) a i p hP
      (haP.unique (Finset.isLeast_min' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP)))
      (hiP.unique (Finset.isGreatest_max' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP))) hp j hjP haj hji =
      ((((I.filter (· ≤ i)).filter (j < ·)).card : ℤ)).negOnePow •
        (deletedP - addedP) := by
    have h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundaryTerm_empty R D s (I.filter (· ≤ i)) a i j p hp hP
      haP hiP hjP haj hji).symm
    unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundaryTerm at h
    dsimp only at h
    simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero, sub_zero,
      Finset.sort_empty, Finset.insert_empty] at h
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_nil R D s _ a i (p + 1) hpE hPE haPE hiPE] at h
    exact h
  have hs : (q + ((((I.filter (· ≤ i)).filter (j < ·)).card : ℤ))).negOnePow =
      (((I.filter (j < ·)).card : ℤ) - (((insert i U).filter (j < ·)).card : ℤ)).negOnePow := by
    rw [hq]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutLeibniz_sign_left I U i j (hc i (Finset.mem_insert_self _ _)).1 hji hmin
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundaryTerm
  dsimp only
  change (((I.filter (j < ·)).card : ℤ) - (((insert i U).filter (j < ·)).card : ℤ)).negOnePow •
      (deleted - added) =
    q.negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R rest
      (s.term (I.filter (· ≤ i)) a i p hP
        (haP.unique (Finset.isLeast_min' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP)))
        (hiP.unique (Finset.isGreatest_max' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP))) hp j hjP haj hji) hcomp
  rw [hd, hA, hterm, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_right, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right, smul_smul,
    ← Int.negOnePow_add, hs]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
