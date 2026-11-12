module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutProductFirstErase
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutProductFirstInsert
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutBoundarySum
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutLeibnizSigns
/-!
概要：先頭切断点より右の実境界項を、右ブロックの境界と先頭 Hom の合成へ同定する。
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
lemma dgNerveCutBoundaryTerm_first_right {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b i j : Fin (n + 1)) (U : Finset (Fin (n + 1)))
    (k p q : ℤ) (hk : k = 2 - (I.card : ℤ) + ((insert i U).card : ℤ))
    (hp : p = 2 - ((I.filter (· ≤ i)).card : ℤ))
    (hq : q = 2 - ((I.filter (i ≤ ·)).card : ℤ) + (U.card : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ x ∈ insert i U, x ∈ I ∧ a < x ∧ x < b) (hmin : ∀ x ∈ U, i < x)
    (hj : j ∈ I) (haj : a < j) (hij : i < j) (hjb : j < b) (hjU : j ∉ U)
    (hP : 2 ≤ (I.filter (· ≤ i)).card)
    (haP : IsLeast ((I.filter (· ≤ i)) : Set (Fin (n + 1))) a)
    (hiP : IsGreatest ((I.filter (· ≤ i)) : Set (Fin (n + 1))) i)
    (hQ : 2 ≤ (I.filter (i ≤ ·)).card)
    (hiQ : IsLeast ((I.filter (i ≤ ·)) : Set (Fin (n + 1))) i)
    (hbQ : IsGreatest ((I.filter (i ≤ ·)) : Set (Fin (n + 1))) b)
    (hcU : ∀ x ∈ U, x ∈ I.filter (i ≤ ·) ∧ i < x ∧ x < b)
    (hcomp : p + (q + 1) = k + 1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundaryTerm R D s I a b (insert i U) j k hk ha hb hc hj haj hjb
      (by simp only [Finset.mem_insert, not_or]; exact ⟨Ne.symm (ne_of_lt hij), hjU⟩) =
      compose R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundaryTerm R D s (I.filter (i ≤ ·)) i b U j q hq hiQ hbQ hcU
        (Finset.mem_filter.mpr ⟨hj, hij.le⟩) hij hjb hjU)
        (s.hom (I.filter (· ≤ i)) a i p hP
          (haP.unique (Finset.isLeast_min' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP)))
          (hiP.unique (Finset.isGreatest_max' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP))) hp) hcomp := by
  have hjS : j ∉ insert i U := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨Ne.symm (ne_of_lt hij), hjU⟩
  have hjQ : j ∈ I.filter (i ≤ ·) := Finset.mem_filter.mpr ⟨hj, hij.le⟩
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
  have hQE : 2 ≤ ((I.filter (i ≤ ·)).erase j).card :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two hiQ.1 hbQ.1 hij hjb
  have hiQE : IsLeast (((I.filter (i ≤ ·)).erase j) : Set (Fin (n + 1))) i :=
    ⟨Finset.mem_erase.mpr ⟨ne_of_lt hij, hiQ.1⟩,
      fun _ hx => hiQ.2 (Finset.mem_erase.mp hx).2⟩
  have hbQE : IsGreatest (((I.filter (i ≤ ·)).erase j) : Set (Fin (n + 1))) b :=
    ⟨Finset.mem_erase.mpr ⟨Ne.symm (ne_of_lt hjb), hbQ.1⟩,
      fun _ hx => hbQ.2 (Finset.mem_erase.mp hx).2⟩
  have hcUE : ∀ x ∈ U, x ∈ (I.filter (i ≤ ·)).erase j ∧ i < x ∧ x < b := by
    intro x hx
    exact ⟨Finset.mem_erase.mpr ⟨fun hxj => hjU (hxj ▸ hx), (hcU x hx).1⟩, (hcU x hx).2⟩
  have hcA : ∀ x ∈ insert j (insert i U), x ∈ I ∧ a < x ∧ x < b := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨hj, haj, hjb⟩
    · exact hc x hx
  have hcUA : ∀ x ∈ insert j U, x ∈ I.filter (i ≤ ·) ∧ i < x ∧ x < b := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨hjQ, hij, hjb⟩
    · exact hcU x hx
  have hkE : k + 1 = 2 - ((I.erase j).card : ℤ) + ((insert i U).card : ℤ) := by
    have hcard := Finset.card_erase_add_one hj
    omega
  have hqE : q + 1 = 2 - (((I.filter (i ≤ ·)).erase j).card : ℤ) + (U.card : ℤ) := by
    have hcard := Finset.card_erase_add_one hjQ
    omega
  have hkA : k + 1 = 2 - (I.card : ℤ) + ((insert j (insert i U)).card : ℤ) := by
    rw [Finset.card_insert_of_notMem hjS]
    push_cast
    omega
  have hqA : q + 1 = 2 - ((I.filter (i ≤ ·)).card : ℤ) + ((insert j U).card : ℤ) := by
    rw [Finset.card_insert_of_notMem hjU]
    push_cast
    omega
  let f := s.hom (I.filter (· ≤ i)) a i p hP
    (haP.unique (Finset.isLeast_min' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP)))
    (hiP.unique (Finset.isGreatest_max' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP))) hp
  let deleted := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s (I.erase j) a b (insert i U)
    (k + 1) hkE hE haE hbE hcE
  let added := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s I a b (insert j (insert i U))
    (k + 1) hkA hI ha hb hcA
  let deletedQ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s ((I.filter (i ≤ ·)).erase j) i b U
    (q + 1) hqE hQE hiQE hbQE hcUE
  let addedQ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s (I.filter (i ≤ ·)) i b (insert j U)
    (q + 1) hqA hQ hiQ hbQ hcUA
  have hd : deleted = compose R deletedQ f hcomp :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree_erase_after_first R D s I a b i j U hij (k + 1) p (q + 1)
      hkE hp hqE hE haE hbE hcE hmin hP haP hiP hQE hiQE hbQE hcUE hcomp
  have hA : added = compose R addedQ f hcomp :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree_insert_after_first R D s I a b i j U hij (k + 1) p (q + 1)
      hkA hp hqA hI ha hb hcA hmin hP haP hiP hQ hiQ hbQ hcUA hcomp
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundaryTerm
  dsimp only
  change (((I.filter (j < ·)).card : ℤ) - (((insert i U).filter (j < ·)).card : ℤ)).negOnePow •
      (deleted - added) =
    _root_.SerrePositivity.DifferentialGraded.compose R (((((I.filter (i ≤ ·)).filter (j < ·)).card : ℤ) -
      ((U.filter (j < ·)).card : ℤ)).negOnePow • (deletedQ - addedQ)) f hcomp
  rw [hd, hA, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_left,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutLeibniz_sign_right I U i j hij]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
