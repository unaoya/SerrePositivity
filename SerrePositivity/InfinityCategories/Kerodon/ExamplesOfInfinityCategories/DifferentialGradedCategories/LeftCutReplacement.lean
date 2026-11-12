module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TopCorrection

/-! # 左切断成分の置換による右辺の変化

概要：内部頂点での左切断成分を置き換えると、その頂点の寄与だけが変わる。
方針：削除集合と右切断は最大頂点を含み、別の左切断は最大頂点が異なることを使う。
規約：HA Proposition 1.3.1.10。使われ方：先頭成分の挿入による脚側・三角形側右辺の変化。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：ある左切断の成分の置換は、別の内部頂点の寄与を変えない。
方針：削除と右切断には最大頂点が残り、左切断の相違は頂点の相違から従う。
規約：HA Proposition 1.3.1.10。使われ方：右辺の変化を一項に制限する。 -/
lemma term_replace_leftCut_of_ne {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ I) (_hai : a < i) (hib : i < b)
    (f : ∀ c d q (hM : 2 ≤ (I.filter (· ≤ i)).card),
      c = (I.filter (· ≤ i)).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      d = (I.filter (· ≤ i)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      q = 2 - ((I.filter (· ≤ i)).card : ℤ) → GradedHom A (s.obj c) (s.obj d) q)
    (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) (hji : j ≠ i) :
    (s.replace (I.filter (· ≤ i)) f).term I a b k hI ha hb hk j hj haj hjb =
      s.term I a b k hI ha hb hk j hj haj hjb := by
  have hbm : b ∈ I := hb ▸ I.max'_mem _
  have hnot : b ∉ I.filter (· ≤ i) := by
    simp only [Finset.mem_filter, not_and]
    exact fun _ => not_le_of_gt hib
  have hE : I.erase j ≠ I.filter (· ≤ i) := by
    intro heq
    exact hnot (heq ▸ Finset.mem_erase.mpr ⟨ne_of_gt hjb, hbm⟩)
  have hR : I.filter (j ≤ ·) ≠ I.filter (· ≤ i) := by
    intro heq
    exact hnot (heq ▸ Finset.mem_filter.mpr ⟨hbm, hjb.le⟩)
  have hL : I.filter (· ≤ j) ≠ I.filter (· ≤ i) := by
    intro heq
    have hmj : j ∈ I.filter (· ≤ i) :=
      heq ▸ (show j ∈ I.filter (· ≤ j) from Finset.mem_filter.mpr ⟨hj, le_rfl⟩)
    have hmi : i ∈ I.filter (· ≤ j) :=
      heq.symm ▸ (show i ∈ I.filter (· ≤ i) from Finset.mem_filter.mpr ⟨hi, le_rfl⟩)
    have hji' : j ≤ i := (Finset.mem_filter.mp hmj).2
    have hij : i ≤ j := (Finset.mem_filter.mp hmi).2
    exact hji (le_antisymm hji' hij)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace, dite_eq_right hE, dite_eq_right hL, dite_eq_right hR]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (term_replace_leftCut_of_ne)


/-- 概要：左切断成分の置換による右辺の変化は、切断頂点の寄与の変化に等しい。
方針：有限和の差を取り、他の内部頂点の寄与の保存で一項だけを残す。
規約：HA Proposition 1.3.1.10。使われ方：δb=p a+r_B と三角形方程式の右辺を計算する。 -/
lemma rhs_replace_leftCut {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ I) (hai : a < i) (hib : i < b)
    (f : ∀ c d q (hM : 2 ≤ (I.filter (· ≤ i)).card),
      c = (I.filter (· ≤ i)).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      d = (I.filter (· ≤ i)).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      q = 2 - ((I.filter (· ≤ i)).card : ℤ) → GradedHom A (s.obj c) (s.obj d) q) :
    (s.replace (I.filter (· ≤ i)) f).rhs I a b k hI ha hb hk - s.rhs I a b k hI ha hb hk =
      (s.replace (I.filter (· ≤ i)) f).term I a b k hI ha hb hk i hi hai hib -
        s.term I a b k hI ha hb hk i hi hai hib := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single (⟨i, hi⟩ : I)]
  · simp only [dite_eq_left (show a < i ∧ i < b from ⟨hai, hib⟩)]
  · intro j _ hji
    by_cases hjint : a < j.val ∧ j.val < b
    · simp only [dite_eq_left hjint]
      rw [term_replace_leftCut_of_ne s I a b k hI ha hb hk i hi hai hib f j.val j.property
        hjint.1 hjint.2 (fun he => hji (Subtype.ext he))]
      exact sub_self _
    · simp only [dite_eq_right hjint, sub_self]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (rhs_replace_leftCut)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
