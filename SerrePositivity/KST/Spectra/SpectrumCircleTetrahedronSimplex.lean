module

public import SerrePositivity.KST.Spectra.SpectrumNativeCircleEvaluationFiber
public import SerrePositivity.KST.Spectra.SpectrumCircleEvaluationCompanion

/-!
概要：元の関手三単体を各 Sp 頂点で評価し、その元の二面を厳密に保持する。
方針：頂点評価と形状の前合成を交換し、元の円の普遍評価の比較二単体を回収する。
規約：三単体や充填を選び直さない。使われ方：元の円評価錐の Hom 正方形による比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleTetrahedronSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の関手三単体を、元の Sp 頂点で評価した同じ三単体。 -/
def circleEvaluationTetrahedronAt (z : Sp.{u} _⦋0⦌) : Sp.{u} _⦋3⦌ :=
  SSet.yonedaEquiv (circleEvaluationTetrahedron ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt z)

/-- 零番目の面は、元の参照零三角形の同じ頂点での評価。 -/
lemma circleEvaluationTetrahedronAt_zero (z : Sp.{u} _⦋0⦌) :
    Sp.{u}.δ 0 (circleEvaluationTetrahedronAt z) =
      SSet.yonedaEquiv (circleZeroFunctorTriangle ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt z) := by
  rw [circleEvaluationTetrahedronAt, ← stdSimplex.yonedaEquiv_δ_comp,
    ← Category.assoc, circleEvaluationTetrahedron_zero]

/-- 頂点で評価した退化零三角形も、元の初辺の始点退化そのもの。 -/
lemma circleZeroDegenerateTriangleAt (z : Sp.{u} _⦋0⦌) :
    SSet.yonedaEquiv (circleZeroDegenerateTriangle ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt z) =
      Sp.{u}.σ 0 (SSet.yonedaEquiv
        ((stdSimplex.δ (2 : Fin 3) ≫ circleZeroFunctorTriangle) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt z)) := by
  rw [circleZeroDegenerateTriangle, Category.assoc, Category.assoc,
    stdSimplex.yonedaEquiv_σ_comp]

/-- 三番目の面は、元の退化零三角形の同じ頂点での評価。 -/
lemma circleEvaluationTetrahedronAt_three (z : Sp.{u} _⦋0⦌) :
    Sp.{u}.δ 3 (circleEvaluationTetrahedronAt z) =
      SSet.yonedaEquiv (circleZeroDegenerateTriangle ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt z) := by
  rw [circleEvaluationTetrahedronAt, ← stdSimplex.yonedaEquiv_δ_comp,
    ← Category.assoc, circleEvaluationTetrahedron_three]

/-- 一番目の面は、元の companion 三角形の同じ頂点での評価。 -/
lemma circleEvaluationTetrahedronAt_one (z : Sp.{u} _⦋0⦌) :
    Sp.{u}.δ 1 (circleEvaluationTetrahedronAt z) =
      SSet.yonedaEquiv (circleZeroCompanionTriangle ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt z) := by
  rw [circleEvaluationTetrahedronAt, ← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc]
  rfl

/-- 二番目の面は、元の普遍評価の生成 loop の coherent Hom 比較二単体そのもの。 -/
lemma circleEvaluationTetrahedronAt_two (z : Sp.{u} _⦋0⦌) :
    Sp.{u}.δ 2 (circleEvaluationTetrahedronAt z) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex
      ((circleEvaluationHomEdge (nativeCotensorInput PointedSimplicialSet.circle z).val).edge) := by
  rw [circleEvaluationTetrahedronAt, ← stdSimplex.yonedaEquiv_δ_comp,
    ← Category.assoc, circleEvaluationTetrahedron_two,
    circleEvaluationFunctorTriangle, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex,
    nativeCircleEvaluationTriangleFamily_fiber]
  exact Equiv.apply_symm_apply _ _

end SerrePositivity.KST.Spectra.OmegaSpectrum
