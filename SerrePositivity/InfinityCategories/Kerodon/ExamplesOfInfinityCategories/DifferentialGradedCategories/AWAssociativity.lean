module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWAssocTerms

/-!
# Alexander–Whitney 成分族の結合律

概要：標準座標の AW 成分族の演算は結合的である。
方針：両辺を二つの切断点の和へ展開し、各項の dg 結合律と和の交換を使う。
規約：標準方程式を仮定する前の任意の成分族に成立する。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の C_Δ の豊穣結合律。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

/-- 概要：右括弧の AW 合成の一切断の項を二切断の和へ展開する。
方針：内側の成分を AW の和にし、斉次合成の線形性を使う。
規約：先の切断点を固定して後の切断点で足す。
使われ方：Kerodon 2.5.8（Tag 00S0） の h ⋆ (g ⋆ f) の二重和。 -/
lemma awTerm_right_expand {w x y z : D} {n : ℕ} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n)
    (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R w x n)
    (J : Finset (Fin (n + 1))) (i : J) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm h (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData g f) J i k hk =
      ∑ j : J.filter (i.val ≤ ·), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWAssocTerms.awNestedRight h g f J i
        ⟨j.val, (Finset.mem_filter.mp j.property).1⟩
        (Finset.mem_filter.mp j.property).2 k hk := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_component, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_right]
  rfl

/-- 概要：左括弧の AW 合成の一切断の項を二切断の和へ展開する。
方針：内側の成分を AW の和にし、斉次合成の線形性を使う。
規約：後の切断点を固定して先の切断点で足す。
使われ方：Kerodon 2.5.8（Tag 00S0） の (h ⋆ g) ⋆ f の二重和。 -/
lemma awTerm_left_expand {w x y z : D} {n : ℕ} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n)
    (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R w x n)
    (J : Finset (Fin (n + 1))) (j : J) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData h g) f J j k hk =
      ∑ i : J.filter (· ≤ j.val), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWAssocTerms.awNestedLeft h g f J
        ⟨i.val, (Finset.mem_filter.mp i.property).1⟩ j
        (Finset.mem_filter.mp i.property).2 k hk := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_component, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_left]
  rfl

/-- 概要：標準成分族の Alexander–Whitney 合成は結合律を満たす。
方針：二つの切断点による和へ展開し、切断順序を交換して dg 結合律を各項に使う。
規約：任意の dg 圏の任意の三つの成分族で成立する。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の単体的豊穣合成の結合律。 -/
lemma awData_assoc {w x y z : D} {n : ℕ} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R y z n)
    (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R w x n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData h (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData g f) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData h g) f := by
  funext a
  rcases a with ⟨⟨J, k⟩, hJ, hk⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData h (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData g f)).component J k hJ hk =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData h g) f).component J k hJ hk
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_component, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_component]
  simp_rw [awTerm_right_expand, awTerm_left_expand]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sum_rightCuts_eq_leftCuts J (fun i j hij ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWAssocTerms.awNestedRight h g f J i j hij k hk)]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWAssocTerms.awNestedRight_eq_left h g f J _ _ _ k hk

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
