module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EquationTransfer
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeData

/-!
概要：実複体の単体データの単射 pullback に沿って、指定集合の HA 方程式を移す。
方針：元の両端を像の最小点・最大点へ戻し、元の pullback 成分と右辺の式を使う。
規約：移す集合の方程式だけを入力にする。使われ方：選択列の終端方程式の元の集合への移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

lemma complexSimplexData_equation_image_of_pullback {m n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (Complex A) n) (α : Fin (m + 1) →o Fin (n + 1))
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (Complex A) m) (h : s.pullback α = t)
    (J : Finset (Fin (m + 1))) (hi : Set.InjOn α (J : Set (Fin (m + 1))))
    (ht : t.Equation J) : s.Equation (J.image α) := by
  intro a b k hI ha hb hk
  have hcard : (J.image α).card = J.card := Finset.card_image_of_injOn hi
  have hJ : 2 ≤ J.card := by omega
  have hkJ : k = 2 - (J.card : ℤ) := by rwa [hcard] at hk
  let a' := J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
  let b' := J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
  have ha' : α a' = a := by
    rw [ha]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone (J.isLeast_min' _) _
  have hb' : α b' = b := by
    rw [hb]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone (J.isGreatest_max' _) _
  have hh := ht a' b' k hJ rfl rfl hkJ
  rw [← h] at hh
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullback_rhs_of_inj _ _ _ _ _ _ _ _ _ _ hi] at hh
  cases ha'
  cases hb'
  exact hh

end SerrePositivity.ComplexLimits
