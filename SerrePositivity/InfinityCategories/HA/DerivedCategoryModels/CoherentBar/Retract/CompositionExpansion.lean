module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedOperators
/-!
概要：符号付き面和と prefix 和への斉次合成を有限和へ分配する。
方針：DGNerve の斉次合成の加法性・符号スカラー保存を、抽象対象の段階で適用する。
規約：始域・中間対象・終域と合成次数の等号を明示的に保持する。
使われ方：実 bar の正規化境界を二つの面和と相殺する prefix 和に分ける。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open DifferentialGraded
variable {R : Type u} [CommRing R] {C : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  {M N P : C} {p q k : ℤ}

lemma dgBarRetract_compose_finite_sum_left {m n : ℕ}
    (a : Fin m → ℤˣ) (b : ℤˣ)
    (f : Fin m → _root_.SerrePositivity.DifferentialGraded.GradedHom R N P q) (g : Fin n → _root_.SerrePositivity.DifferentialGraded.GradedHom R N P q)
    (e : _root_.SerrePositivity.DifferentialGraded.GradedHom R M N p) (hk : p + q = k) :
    _root_.SerrePositivity.DifferentialGraded.compose R ((∑ i, a i • f i) + b • ∑ j, g j) e hk =
      (∑ i, a i • _root_.SerrePositivity.DifferentialGraded.compose R (f i) e hk) + b • ∑ j, _root_.SerrePositivity.DifferentialGraded.compose R (g j) e hk := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_left]

lemma dgBarRetract_compose_finite_sum_right {m n : ℕ}
    (a : Fin m → ℤˣ) (b : ℤˣ)
    (f : Fin m → _root_.SerrePositivity.DifferentialGraded.GradedHom R M N p) (g : Fin n → _root_.SerrePositivity.DifferentialGraded.GradedHom R M N p)
    (e : _root_.SerrePositivity.DifferentialGraded.GradedHom R N P q) (hk : p + q = k) :
    _root_.SerrePositivity.DifferentialGraded.compose R e ((∑ i, a i • f i) + b • ∑ j, g j) hk =
      (∑ i, a i • _root_.SerrePositivity.DifferentialGraded.compose R e (f i) hk) + b • ∑ j, _root_.SerrePositivity.DifferentialGraded.compose R e (g j) hk := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_right, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_right, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_right]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
