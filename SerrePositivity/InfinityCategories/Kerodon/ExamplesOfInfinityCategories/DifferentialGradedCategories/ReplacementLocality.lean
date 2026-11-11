module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FixedHomReplacement
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EquationTransfer

/-! # 成分置換の局所性

概要：置換する集合を含まない集合では右辺と方程式は保存される。
方針：削除集合と左右切断集合が元の集合の部分集合であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：境界の未知成分を挿入しても既知方程式が壊れないこと。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：置換集合を含まない集合の内部点の寄与は変わらない。
方針：削除集合と左右の切断集合が置換集合と異なることから成分の置換を消す。
規約：HA Proposition 1.3.1.10。使われ方：未知成分の挿入の局所性。 -/
lemma term_replace_of_not_subset {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (M : Finset (Fin (n + 1)))
    (f : ∀ a b k (hM : 2 ≤ M.card),
      a = M.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) → b = M.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      k = 2 - (M.card : ℤ) → GradedHom A (s.obj a) (s.obj b) k)
    (I : Finset (Fin (n + 1))) (hnot : ¬ M ⊆ I)
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I)
    (haj : a < j) (hjb : j < b) :
    (s.replace M f).term I a b k hI ha hb hk j hj haj hjb =
      s.term I a b k hI ha hb hk j hj haj hjb := by
  have he : I.erase j ≠ M := fun h => hnot (h ▸ Finset.erase_subset j I)
  have hl : I.filter (· ≤ j) ≠ M := fun h => hnot (h ▸ Finset.filter_subset _ _)
  have hr : I.filter (j ≤ ·) ≠ M := fun h => hnot (h ▸ Finset.filter_subset _ _)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace, dite_eq_right he, dite_eq_right hl, dite_eq_right hr]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (term_replace_of_not_subset)


/-- 概要：置換集合を含まない集合の方程式の右辺は変わらない。
方針：各内部点の寄与の局所性を有限和に適用する。
規約：HA Proposition 1.3.1.10。使われ方：既知方程式の右辺の保存。 -/
lemma rhs_replace_of_not_subset {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (M : Finset (Fin (n + 1)))
    (f : ∀ a b k (hM : 2 ≤ M.card),
      a = M.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) → b = M.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      k = 2 - (M.card : ℤ) → GradedHom A (s.obj a) (s.obj b) k)
    (I : Finset (Fin (n + 1))) (hnot : ¬ M ⊆ I)
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (s.replace M f).rhs I a b k hI ha hb hk = s.rhs I a b k hI ha hb hk := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  apply Finset.sum_congr rfl
  intro j _
  by_cases hint : a < j.val ∧ j.val < b
  · simp only [dite_eq_left hint, term_replace_of_not_subset s M f I hnot]
  · simp only [dite_eq_right hint]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (rhs_replace_of_not_subset)


/-- 概要：置換集合を含まない集合で成り立つ方程式は置換後も成り立つ。
方針：対象集合自身の成分と右辺がともに保存されることを使う。
規約：HA Proposition 1.3.1.10。使われ方：未知成分の挿入後の全既知方程式を一括して検証する。 -/
lemma equation_replace_of_not_subset {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (M : Finset (Fin (n + 1)))
    (f : ∀ a b k (hM : 2 ≤ M.card),
      a = M.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) → b = M.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      k = 2 - (M.card : ℤ) → GradedHom A (s.obj a) (s.obj b) k)
    (I : Finset (Fin (n + 1))) (hnot : ¬ M ⊆ I) (heq : s.Equation I) :
    (s.replace M f).Equation I := by
  intro a b k hI ha hb hk
  have hne : I ≠ M := by
    intro h
    subst I
    exact hnot Finset.Subset.rfl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_hom_of_ne s M f I a b k hI ha hb hk hne,
    rhs_replace_of_not_subset s M f I hnot]
  exact heq a b k hI ha hb hk

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (equation_replace_of_not_subset)


/-- 概要：固定一射による置換は置換集合を含まない集合の右辺を保存する。
方針：固定一射の置換を一般の射族の置換に展開し局所性を使う。
規約：HA Proposition 1.3.1.10。使われ方：D 側成分を挿入しても先頭右辺を保存する。 -/
lemma rhs_replaceFixed_of_not_subset {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (M : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hM : 2 ≤ M.card) (ha : a = M.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM))
    (hb : b = M.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM)) (hk : k = 2 - (M.card : ℤ))
    (f : GradedHom A (s.obj a) (s.obj b) k)
    (I : Finset (Fin (n + 1))) (hnot : ¬ M ⊆ I)
    (c d : Fin (n + 1)) (l : ℤ) (hI : 2 ≤ I.card)
    (hc : c = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hd : d = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hl : l = 2 - (I.card : ℤ)) :
    (s.replaceFixed M a b k hM ha hb hk f).rhs I c d l hI hc hd hl =
      s.rhs I c d l hI hc hd hl := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replaceFixed
  exact s.rhs_replace_of_not_subset M _ I hnot c d l hI hc hd hl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (rhs_replaceFixed_of_not_subset)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
