module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveOppositeTerms
/-!
概要：符号付き実成分反転は、dg nerve の全 HA 微分方程式を保存する。
方針：内部点の反転の実全単射で有限和を移し、同じ全体符号を微分と交換する。
規約：方程式を追加仮定せず、元の同じ単体の方程式から得る。
使われ方：β5 の dg 反対模型の実単体操作。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGNerveOppositeIndex
open scoped BigOperators
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {n : ℕ}
/-- 元の実頂点部分集合と反転集合の、内部点の全単射。 -/
def reverseElementEquiv (I : Finset (Fin (n + 1))) : I ≃ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I where
  toFun j := ⟨j.val.rev, by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.mem_reverse, Fin.rev_rev] using j.property⟩
  invFun j := ⟨j.val.rev, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.mem_reverse I j.val).mp j.property⟩
  left_inv _ := Subtype.ext (Fin.rev_rev _)
  right_inv _ := Subtype.ext (Fin.rev_rev _)
/-- HA 方程式の全右辺は、同じ反転集合の全右辺の全体符号倍。 -/
lemma op_rhs (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op s).rhs I a b k hI ha hb hk =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign I.card • s.rhs (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I) b.rev a.rev k (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.two_le_card_reverse hI)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_min hI hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_max hI ha)
        (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse] using hk) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs]
  rw [Finset.smul_sum]
  apply Fintype.sum_equiv (reverseElementEquiv I)
  intro j
  change (if h : a < j.val ∧ j.val < b then _ else 0) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign I.card • (if h : b.rev < j.val.rev ∧ j.val.rev < a.rev then _ else 0)
  by_cases h : a < j.val ∧ j.val < b
  · have hr : b.rev < j.val.rev ∧ j.val.rev < a.rev :=
      ⟨Fin.rev_lt_rev.mpr h.2, Fin.rev_lt_rev.mpr h.1⟩
    rw [dite_eq_left h, dite_eq_left hr]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op_term s I a b k hI ha hb hk j.val j.property h.1 h.2
  · have hr : ¬ (b.rev < j.val.rev ∧ j.val.rev < a.rev) := by
      intro hh
      exact h ⟨Fin.rev_lt_rev.mp hh.2, Fin.rev_lt_rev.mp hh.1⟩
    rw [dite_eq_right h, dite_eq_right hr, smul_zero]
/-- 全 HA 方程式を満たす同じ単体を、実 dg 反対模型の単体へ送る。 -/
def opSimplex (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R Dᵒᵖ n where
  toSimplexData := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op s.toSimplexData
  equation I a b k hI ha hb hk := by
    change _root_.SerrePositivity.DifferentialGraded.differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign I.card • s.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I) b.rev a.rev k
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.two_le_card_reverse hI) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_min hI hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_max hI ha)
      (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse] using hk)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_units_smul, s.equation, op_rhs]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
