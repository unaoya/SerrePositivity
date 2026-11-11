module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGNativeActionFixed
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGActionUnit
public import SerrePositivity.KST.SConstruction.DGFunctorNativeSimplexCoherence

/-! # 元の恒等関手による全 native Perf 右作用の単位則
概要：元の恒等 dg 入力とその全退化を作用させると、元の全 Perf 単体を回収する。
方針：固定入力の全単体的回収と、元のラベル付き dg 作用の厳密単位を使う。
規約：元の閉単位と増大の同じ単体族。使われ方：厳密豊穣 Perf 作用の単位。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の恒等関手の全 native 単位単体は、同じ対象を指定した元の定数単体。 -/
lemma dgFunctorNativeIdentitySimplex_point (N : ℕ) :
    dgFunctorNativeIdentitySimplex A D N =
      dgNativePointSimplex A (DGFunctor A D D) (DGFunctor.id D) N := rfl

/-- 元の恒等関手の native 単位単体を作用させると、元の全 Perf 単体を回収する。 -/
lemma presentedPerfectDGNativeActionSimplex_unit {N : ℕ}
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (PresentedPerfectDGObject A D) N) :
    presentedPerfectDGNativeActionSimplex A D D x (dgFunctorNativeIdentitySimplex A D N) = x := by
  rw [dgFunctorNativeIdentitySimplex_point, presentedPerfectDGNativeActionSimplex_fixed,
    presentedPerfectDGAction_id]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_id x.toSimplexData

/-- 元の恒等関手を選ぶ単位射による全単体的右作用は、元の右単位射。 -/
lemma presentedPerfectDGNativeCoreAction_unit :
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A D)) ⊗ₘ
        presentedPerfectDGNativeParameterPoint A D D (DGFunctor.id D)) ≫
        presentedPerfectDGNativeCoreAction A D D =
      (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A D))).hom := by
  rw [presentedPerfectDGNativeCoreAction_fixed, presentedPerfectDGAction_id,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id, Category.comp_id]

/-- 元の恒等関手を選ぶ単位射の curry 像は、関手空間の元の豊穣恒等射。 -/
lemma presentedPerfectDGNativeFamilyMap_unit :
    presentedPerfectDGNativeParameterPoint A D D (DGFunctor.id D) ≫
        presentedPerfectDGNativeFamilyMap A D D =
      MonoidalClosed.id (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A D)) := by
  rw [presentedPerfectDGNativeFamilyMap_fixed, presentedPerfectDGAction_id, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id]
  simp only [curry', Category.comp_id, MonoidalClosed.id]

end SerrePositivity.KST.SConstruction
