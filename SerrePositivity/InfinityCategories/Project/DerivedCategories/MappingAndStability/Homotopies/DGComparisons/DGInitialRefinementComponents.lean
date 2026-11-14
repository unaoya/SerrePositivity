module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGSimplexDataInitialRefinement

/-! # 任意次数の始点細分の成分の厳密な回収

概要：始点を含む成分は同じ閉前合成、始点を含まない成分は元のままと異種等号で照合する。
方針：二点以上の部分集合の両端は狭義に増加し、終点は必ず正であることを使う。
規約：対象のラベル輸送を保持する。使われ方：高次指定面の重なりと残差の計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 二点以上の部分集合の指定両端は、狭義に増加する。 -/
lemma dgSimplexIndex_endpoints_lt {n : ℕ} (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) : a < b := by
  rw [ha, hb]
  exact I.min'_lt_max'_of_card (by omega)

variable (A D) {n : ℕ} (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (t.obj 0))

/-- 始点を含む成分は、元の指定成分を同じ閉射で前合成したもの。 -/
lemma dgSimplexDataInitialRefinement_hom_from_zero
    (I : Finset (Fin (n + 1))) (b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : (0 : Fin (n + 1)) = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement A D t q s).hom I 0 b k hI ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k (t.hom I 0 b k hI ha hb hk) s) := by
  have hb0 : b ≠ 0 := ne_of_gt (dgSimplexIndex_endpoints_lt I 0 b hI ha hb)
  exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear_from_zero A D t.obj q s b hb0 k
    (t.hom I 0 b k hI ha hb hk))).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ rfl _)

/-- 正始点の成分は、元の指定成分とそのまま異種等号で一致する。 -/
lemma dgSimplexDataInitialRefinement_hom_ne_zero
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement A D t q s).hom I a b k hI ha hb hk)
      (t.hom I a b k hI ha hb hk) := by
  have hb0 : b ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le a)
    (dgSimplexIndex_endpoints_lt I a b hI ha hb))
  exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear_of_ne_zero A D t.obj q s a b ha0 hb0 k
    (t.hom I a b k hI ha hb hk))).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ rfl _)

/-- 始点を含む rhs は、元の指定 rhs の同じ閉前合成。 -/
lemma dgSimplexDataInitialRefinement_rhs_from_zero
    (I : Finset (Fin (n + 1))) (b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : (0 : Fin (n + 1)) = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement A D t q s).rhs I 0 b k hI ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (k + 1) (t.rhs I 0 b k hI ha hb hk) s) := by
  have hb0 : b ≠ 0 := ne_of_gt (dgSimplexIndex_endpoints_lt I 0 b hI ha hb)
  exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement_rhs A D t q s I 0 b k hI ha hb hk).symm).trans
    ((heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear_from_zero A D t.obj q s b hb0 (k + 1)
      (t.rhs I 0 b k hI ha hb hk))).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ rfl _))

/-- 正始点の rhs は、元の指定 rhs とそのまま異種等号で一致する。 -/
lemma dgSimplexDataInitialRefinement_rhs_ne_zero
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a ≠ 0) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement A D t q s).rhs I a b k hI ha hb hk)
      (t.rhs I a b k hI ha hb hk) := by
  have hb0 : b ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le a)
    (dgSimplexIndex_endpoints_lt I a b hI ha hb))
  exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement_rhs A D t q s I a b k hI ha hb hk).symm).trans
    ((heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSourceRefinementHomLinear_of_ne_zero A D t.obj q s a b ha0 hb0 (k + 1)
      (t.rhs I a b k hI ha hb hk))).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ rfl _))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
