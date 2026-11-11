module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutBoundaryFirstRight
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutBoundaryFirstLeft
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
/-!
概要：非空切断の実境界和を、先頭切断点の左右の二合成へ同定する。
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
lemma dgNerveFiniteSubset_sum {α : Type u} [Fintype α] [DecidableEq α]
    (I : Finset α) {M : Type v} [AddCommMonoid M] (f : I → M) :
    (∑ j : I, f j) = ∑ j : α, if h : j ∈ I then f ⟨j, h⟩ else 0 := by
  simpa only [Finset.univ_eq_attach] using Finset.sum_attach_eq_sum_dite I f
/-- 元の実切断合成の境界項と符号付き全和の照合。 -/
lemma dgNerveCutBoundarySum_first {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (I : Finset (Fin (n + 1))) (a b i : Fin (n + 1)) (U : Finset (Fin (n + 1)))
    (k p q : ℤ) (hk : k = 2 - (I.card : ℤ) + ((insert i U).card : ℤ))
    (hp : p = 2 - ((I.filter (· ≤ i)).card : ℤ))
    (hq : q = 2 - ((I.filter (i ≤ ·)).card : ℤ) + (U.card : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hc : ∀ x ∈ insert i U, x ∈ I ∧ a < x ∧ x < b) (hmin : ∀ x ∈ U, i < x)
    (hP : 2 ≤ (I.filter (· ≤ i)).card)
    (haP : IsLeast ((I.filter (· ≤ i)) : Set (Fin (n + 1))) a)
    (hiP : IsGreatest ((I.filter (· ≤ i)) : Set (Fin (n + 1))) i)
    (hQ : 2 ≤ (I.filter (i ≤ ·)).card)
    (hiQ : IsLeast ((I.filter (i ≤ ·)) : Set (Fin (n + 1))) i)
    (hbQ : IsGreatest ((I.filter (i ≤ ·)) : Set (Fin (n + 1))) b)
    (hcU : ∀ x ∈ U, x ∈ I.filter (i ≤ ·) ∧ i < x ∧ x < b) (hsum : p + q = k) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundarySum R D s I a b (insert i U) k hk ha hb hc =
      compose R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundarySum R D s (I.filter (i ≤ ·)) i b U q hq hiQ hbQ hcU)
        (s.hom (I.filter (· ≤ i)) a i p hP
          (haP.unique (Finset.isLeast_min' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP)))
          (hiP.unique (Finset.isGreatest_max' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP))) hp) (by omega) +
      q.negOnePow • _root_.SerrePositivity.DifferentialGraded.compose R
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProductAtDegree R D s (I.filter (i ≤ ·)) i b U q hq hQ hiQ hbQ hcU)
        (s.rhs (I.filter (· ≤ i)) a i p hP
          (haP.unique (Finset.isLeast_min' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP)))
          (hiP.unique (Finset.isGreatest_max' _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hP))) hp) (by omega) := by
  have hiI := (hc i (Finset.mem_insert_self _ _)).1
  have hai := (hc i (Finset.mem_insert_self _ _)).2.1
  have hib := (hc i (Finset.mem_insert_self _ _)).2.2
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundarySum _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_right, Finset.smul_sum]
  rw [dgNerveFiniteSubset_sum I, dgNerveFiniteSubset_sum (I.filter (i ≤ ·)),
    dgNerveFiniteSubset_sum (I.filter (· ≤ i)), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hjI : j ∈ I
  · rcases lt_trichotomy j i with hji | heq | hij
    · have hjP : j ∈ I.filter (· ≤ i) := Finset.mem_filter.mpr ⟨hjI, hji.le⟩
      have hjQ : j ∉ I.filter (i ≤ ·) := by
        intro hx
        exact not_le_of_gt hji (Finset.mem_filter.mp hx).2
      have hjU : j ∉ U := fun hx => lt_asymm hji (hmin j hx)
      have hjS : j ∉ insert i U := by
        simp only [Finset.mem_insert, not_or]
        exact ⟨ne_of_lt hji, hjU⟩
      by_cases haj : a < j
      · have hjb := lt_trans hji hib
        have hfull : a < j ∧ j < b ∧ j ∉ insert i U := ⟨haj, hjb, hjS⟩
        have hleft : a < j ∧ j < i := ⟨haj, hji⟩
        simp only [dite_eq_left hjI, dite_eq_right hjQ, dite_eq_left hjP,
          dite_eq_left hfull, dite_eq_left hleft, zero_add]
        exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundaryTerm_first_left R D s I a b i j U k p q hk hp hq ha hb hc
          hmin hjI haj hji hjb hjU hP haP hiP hQ hiQ hbQ hcU (by omega)
      · have hfull : ¬(a < j ∧ j < b ∧ j ∉ insert i U) := fun h => haj h.1
        have hleft : ¬(a < j ∧ j < i) := fun h => haj h.1
        simp only [dite_eq_left hjI, dite_eq_right hjQ, dite_eq_left hjP,
          dite_eq_right hfull, dite_eq_right hleft, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero]
    · subst j
      have hiPmem : i ∈ I.filter (· ≤ i) := Finset.mem_filter.mpr ⟨hiI, le_rfl⟩
      have hiQmem : i ∈ I.filter (i ≤ ·) := Finset.mem_filter.mpr ⟨hiI, le_rfl⟩
      have hfull : ¬(a < i ∧ i < b ∧ i ∉ insert i U) :=
        fun h => h.2.2 (Finset.mem_insert_self _ _)
      have hright : ¬(i < i ∧ i < b ∧ i ∉ U) := fun h => lt_irrefl i h.1
      have hleft : ¬(a < i ∧ i < i) := fun h => lt_irrefl i h.2
      simp only [dite_eq_left hiI, dite_eq_left hiPmem, dite_eq_left hiQmem,
        dite_eq_right hfull, dite_eq_right hright, dite_eq_right hleft,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero]
    · have hjQ : j ∈ I.filter (i ≤ ·) := Finset.mem_filter.mpr ⟨hjI, hij.le⟩
      have hjP : j ∉ I.filter (· ≤ i) := by
        intro hx
        exact not_le_of_gt hij (Finset.mem_filter.mp hx).2
      have haj := lt_trans hai hij
      by_cases h : j < b ∧ j ∉ U
      · have hjS : j ∉ insert i U := by
          simp only [Finset.mem_insert, not_or]
          exact ⟨Ne.symm (ne_of_lt hij), h.2⟩
        have hfull : a < j ∧ j < b ∧ j ∉ insert i U := ⟨haj, h.1, hjS⟩
        have hright : i < j ∧ j < b ∧ j ∉ U := ⟨hij, h⟩
        simp only [dite_eq_left hjI, dite_eq_left hjQ, dite_eq_right hjP,
          dite_eq_left hfull, dite_eq_left hright, add_zero]
        exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundaryTerm_first_right R D s I a b i j U k p q hk hp hq hI ha hb hc
          hmin hjI haj hij h.1 h.2 hP haP hiP hQ hiQ hbQ hcU (by omega)
      · have hfull : ¬(a < j ∧ j < b ∧ j ∉ insert i U) := by
          intro hfull
          exact h ⟨hfull.2.1, fun hjU => hfull.2.2 (Finset.mem_insert_of_mem hjU)⟩
        have hright : ¬(i < j ∧ j < b ∧ j ∉ U) := fun hr => h hr.2
        simp only [dite_eq_left hjI, dite_eq_left hjQ, dite_eq_right hjP,
          dite_eq_right hfull, dite_eq_right hright, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, zero_add]
  · have hjP : j ∉ I.filter (· ≤ i) := fun hx => hjI (Finset.mem_filter.mp hx).1
    have hjQ : j ∉ I.filter (i ≤ ·) := fun hx => hjI (Finset.mem_filter.mp hx).1
    simp only [dite_eq_right hjI, dite_eq_right hjP, dite_eq_right hjQ, zero_add]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
