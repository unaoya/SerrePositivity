module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGGradedClosedPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGClosedCompositionLinear
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomTransport

/-! # 頂点零の閉細分に伴う全次数 Hom の線形写像

概要：頂点零だけを q に置き換え、零始点の Hom は閉前合成、正始点の Hom は対象輸送で写す。
方針：対象輸送と固定閉射による線形前合成を合成する。
規約：終点零の Hom は未使用なので零写像とする。使われ方：任意次数の単体の始点細分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable {n : ℕ} (o : Fin (n + 1) → D) (q : D)

/-- 頂点零だけを指定新対象に置き換える。 -/
def dgSourceRefinementObj (i : Fin (n + 1)) : D := if i = 0 then q else o i

omit [CommRing A] [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] in
/-- 新しい始対象は指定した q。 -/
lemma dgSourceRefinementObj_zero : dgSourceRefinementObj D o q 0 = q := ite_eq_left rfl

omit [CommRing A] [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] in
/-- 正の番号の対象は元のまま。 -/
lemma dgSourceRefinementObj_ne_zero (i : Fin (n + 1)) (hi : i ≠ 0) :
    dgSourceRefinementObj D o q i = o i := ite_eq_right hi

variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (o 0))

/-- 閉始点細分に伴う各 Hom の全次数線形写像。 -/
def dgSourceRefinementHomLinear (a b : Fin (n + 1)) (k : ℤ) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (o a) (o b) k →ₗ[A]
      _root_.SerrePositivity.DifferentialGraded.GradedHom A (dgSourceRefinementObj D o q a) (dgSourceRefinementObj D o q b) k := by
  by_cases hb : b = 0
  · exact 0
  · by_cases ha : a = 0
    · subst a
      change _root_.SerrePositivity.DifferentialGraded.GradedHom A (o 0) (o b) k →ₗ[A]
        _root_.SerrePositivity.DifferentialGraded.GradedHom A q (dgSourceRefinementObj D o q b) k
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (rfl : q = q)
        (dgSourceRefinementObj_ne_zero D o q b hb).symm (rfl : k = k)).toLinearMap.comp
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgZeroPrecomposeLinear A D (closedHomEquiv A D _ _ s).val k)
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (dgSourceRefinementObj_ne_zero D o q a ha).symm
        (dgSourceRefinementObj_ne_zero D o q b hb).symm (rfl : k = k)).toLinearMap

/-- 正始点・正終点の Hom の写像は、対象の等式による輸送そのもの。 -/
lemma dgSourceRefinementHomLinear_of_ne_zero (a b : Fin (n + 1)) (ha : a ≠ 0) (hb : b ≠ 0)
    (k : ℤ) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A (o a) (o b) k) :
    dgSourceRefinementHomLinear A D o q s a b k f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (dgSourceRefinementObj_ne_zero D o q a ha).symm
        (dgSourceRefinementObj_ne_zero D o q b hb).symm rfl f := by
  simp only [dgSourceRefinementHomLinear, dite_eq_right hb, dite_eq_right ha]
  rfl

/-- 零始点・正終点の Hom の写像は、閉前合成と終対象の等式輸送。 -/
lemma dgSourceRefinementHomLinear_from_zero (b : Fin (n + 1)) (hb : b ≠ 0)
    (k : ℤ) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A (o 0) (o b) k) :
    dgSourceRefinementHomLinear A D o q s 0 b k f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (rfl : q = q) (dgSourceRefinementObj_ne_zero D o q b hb).symm rfl
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k f s) := by
  simp only [dgSourceRefinementHomLinear, dite_eq_right hb]
  rfl

/-- 対象・次数の同じ等式輸送をした線形写像は、実微分と可換。 -/
lemma dgSourceRefinementHomLinear_differential (a b : Fin (n + 1)) (k : ℤ)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A (o a) (o b) k) :
    _root_.SerrePositivity.DifferentialGraded.differential A (dgSourceRefinementHomLinear A D o q s a b k f) =
      dgSourceRefinementHomLinear A D o q s a b (k + 1) (_root_.SerrePositivity.DifferentialGraded.differential A f) := by
  by_cases hb : b = 0
  · simp only [dgSourceRefinementHomLinear, dite_eq_left hb, LinearMap.zero_apply,
      _root_.SerrePositivity.DifferentialGraded.differential, map_zero]
  · by_cases ha : a = 0
    · subst a
      rw [dgSourceRefinementHomLinear_from_zero A D o q s b hb k,
        dgSourceRefinementHomLinear_from_zero A D o q s b hb (k + 1)]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_differential (A := A) (rfl : q = q)
        (dgSourceRefinementObj_ne_zero D o q b hb).symm rfl
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k f s)).symm.trans
            (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (rfl : q = q)
              (dgSourceRefinementObj_ne_zero D o q b hb).symm (rfl : k + 1 = k + 1))
                (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_d A D k (k + 1) rfl f s))
    · rw [dgSourceRefinementHomLinear_of_ne_zero A D o q s a b ha hb k,
        dgSourceRefinementHomLinear_of_ne_zero A D o q s a b ha hb (k + 1)]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_differential _ _ rfl f).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
