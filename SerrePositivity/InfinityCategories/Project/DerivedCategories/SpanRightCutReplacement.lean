module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TopCorrection

/-! # 右切断成分の置換による右辺の変化

概要：内部頂点での右切断成分を置き換えると、その頂点の寄与だけが変わる。
方針：削除集合と左切断は最小頂点を含み、別の右切断は最小頂点が異なることを使う。
規約：HA Proposition 1.3.1.10。使われ方：後続成分の挿入による脚側・三角形側右辺の変化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：ある右切断の成分の置換は、別の内部頂点の寄与を変えない。
方針：削除と左切断には最小頂点が残り、右切断の相違は頂点の相違から従う。
規約：HA Proposition 1.3.1.10。使われ方：右辺の変化を一項に制限する。 -/
lemma term_replace_rightCut_of_ne {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ I) (_hai : a < i) (_hib : i < b)
    (f : ∀ c d q (hM : 2 ≤ (I.filter (i ≤ ·)).card),
      c = (I.filter (i ≤ ·)).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      d = (I.filter (i ≤ ·)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      q = 2 - ((I.filter (i ≤ ·)).card : ℤ) → GradedHom A (s.obj c) (s.obj d) q)
    (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) (hji : j ≠ i) :
    (s.replace (I.filter (i ≤ ·)) f).term I a b k hI ha hb hk j hj haj hjb =
      s.term I a b k hI ha hb hk j hj haj hjb := by
  have ham : a ∈ I := ha ▸ I.min'_mem _
  have hnot : a ∉ I.filter (i ≤ ·) := by
    simp only [Finset.mem_filter, not_and]
    exact fun _ => not_le_of_gt _hai
  have hE : I.erase j ≠ I.filter (i ≤ ·) := by
    intro heq
    exact hnot (heq ▸ Finset.mem_erase.mpr ⟨ne_of_lt haj, ham⟩)
  have hL : I.filter (· ≤ j) ≠ I.filter (i ≤ ·) := by
    intro heq
    exact hnot (heq ▸ Finset.mem_filter.mpr ⟨ham, haj.le⟩)
  have hR : I.filter (j ≤ ·) ≠ I.filter (i ≤ ·) := by
    intro heq
    have hmj : j ∈ I.filter (i ≤ ·) :=
      heq ▸ (show j ∈ I.filter (j ≤ ·) from Finset.mem_filter.mpr ⟨hj, le_rfl⟩)
    have hmi : i ∈ I.filter (j ≤ ·) :=
      heq.symm ▸ (show i ∈ I.filter (i ≤ ·) from Finset.mem_filter.mpr ⟨hi, le_rfl⟩)
    exact hji (le_antisymm (Finset.mem_filter.mp hmi).2 (Finset.mem_filter.mp hmj).2)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace, dite_eq_right hE, dite_eq_right hL, dite_eq_right hR]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (term_replace_rightCut_of_ne)


/-- 概要：右切断成分の置換による右辺の変化は、切断頂点の寄与の変化に等しい。
方針：有限和の差を取り、他の内部頂点の寄与の保存で一項だけを残す。
規約：HA Proposition 1.3.1.10。使われ方：後続成分との合成による右辺の変化を計算する。 -/
lemma rhs_replace_rightCut {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ I) (hai : a < i) (hib : i < b)
    (f : ∀ c d q (hM : 2 ≤ (I.filter (i ≤ ·)).card),
      c = (I.filter (i ≤ ·)).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      d = (I.filter (i ≤ ·)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      q = 2 - ((I.filter (i ≤ ·)).card : ℤ) → GradedHom A (s.obj c) (s.obj d) q) :
    (s.replace (I.filter (i ≤ ·)) f).rhs I a b k hI ha hb hk - s.rhs I a b k hI ha hb hk =
      (s.replace (I.filter (i ≤ ·)) f).term I a b k hI ha hb hk i hi hai hib -
        s.term I a b k hI ha hb hk i hi hai hib := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single (⟨i, hi⟩ : I)]
  · simp only [dite_eq_left (show a < i ∧ i < b from ⟨hai, hib⟩)]
  · intro j _ hji
    by_cases hjint : a < j.val ∧ j.val < b
    · simp only [dite_eq_left hjint]
      rw [term_replace_rightCut_of_ne s I a b k hI ha hb hk i hi hai hib f j.val j.property
        hjint.1 hjint.2 (fun he => hji (Subtype.ext he))]
      exact sub_self _
    · simp only [dite_eq_right hjint, sub_self]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (rhs_replace_rightCut)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
