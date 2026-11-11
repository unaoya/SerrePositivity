module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TopCorrection

/-! # 削除集合と同定した集合の成分置換

概要：内部頂点の削除集合に等しい別の表示の集合を置換しても、右辺の変化は符号付きの成分差。
方針：集合の等式を消去し、既存の削除成分の置換公式を適用する。
規約：HA Proposition 1.3.1.10。使われ方：D 側集合を全体集合の削除集合と同定する。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：内部削除集合に等しい集合の成分置換による右辺の変化は、符号付きの成分差。
方針：集合の等式を消去し、成分の有効性の証明を証明の一意性で同定する。
規約：HA Proposition 1.3.1.10。使われ方：D 側成分を挿入した三角形右辺の計算。 -/
lemma rhs_replace_of_erase_eq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ I) (hai : a < i) (hib : i < b)
    (M : Finset (Fin (n + 1))) (hEq : I.erase i = M)
    (hM : 2 ≤ M.card) (haM : a = M.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM))
    (hbM : b = M.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM)) (hkM : k + 1 = 2 - (M.card : ℤ))
    (f : ∀ c d q (hN : 2 ≤ M.card),
      c = M.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hN) → d = M.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hN) →
      q = 2 - (M.card : ℤ) → GradedHom A (s.obj c) (s.obj d) q) :
    (s.replace M f).rhs I a b k hI ha hb hk - s.rhs I a b k hI ha hb hk =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I i • (f a b (k + 1) hM haM hbM hkM - s.hom M a b (k + 1) hM haM hbM hkM) := by
  cases hEq
  exact s.rhs_replace I a b k hI ha hb hk i hi hai hib f

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (rhs_replace_of_erase_eq)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
