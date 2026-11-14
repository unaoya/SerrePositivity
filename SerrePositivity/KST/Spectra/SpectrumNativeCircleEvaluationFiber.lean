module

public import SerrePositivity.KST.Spectra.SpectrumNativeCotensorFiber
public import SerrePositivity.KST.Spectra.SpectrumCircleEvaluationHom
public import SerrePositivity.KST.Spectra.SpectrumNativeCircleEvaluationSquare
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation

/-!
概要：元の Sp の各頂点での円評価四角形と、三角形の BF 写像空間による厳密な表示。
方針：逆射が選んだ入力の豊穣評価へ制限し、元の生成 loop の Hom 比較を回収する。
規約：四角形と円のホモトピーを選び直さない。使われ方：点ごとの極限性の検査。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance nativeCircleFiberSpectrumSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の Sp の頂点での円評価四角形。元の族の制限そのもの。 -/
def nativeCircleEvaluationSquare (z : Sp.{u} _⦋0⦌) :
    (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ Sp.{u} :=
  lift (SSet.const z) (𝟙 _) ≫ nativeCircleEvaluationSquareFamily

/-- 点ごとの四角形は、関手 quasicategory の同じ四角形の頂点評価。 -/
lemma nativeCircleEvaluationSquare_evaluation (z : Sp.{u} _⦋0⦌) :
    nativeCircleEvaluationSquare z = circleEvaluationFunctorSquare ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt z := by
  rw [nativeCircleEvaluationSquare, nativeCircleEvaluationSquareFamily,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex, curry_uncurry]

/-- 点ごとの四角形の二つの非対角頂点は、元の一点 BF スペクトルの標準頂点。 -/
lemma nativeCircleEvaluationSquare_zeroCorner (z : Sp.{u} _⦋0⦌) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (nativeCircleEvaluationSquare z) i i.rev =
      pointZeroVertex.vertex := by
  rw [nativeCircleEvaluationSquare_evaluation]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt z).app (Opposite.op ⦋0⦌)
    (circleEvaluationFunctorSquare.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm i.rev)) = _
  have h := congrArg SSet.yonedaEquiv (circleEvaluationFunctorSquare_zeroCorner.{u} i)
  change circleEvaluationFunctorSquare.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm i.rev) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (constantZeroDiagram Sp.{u}) at h
  rw [h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  rfl

/-- 点ごとの四角形の非対角頂点は、Sp の実際の零対象。 -/
lemma nativeCircleEvaluationSquare_zeroCorner_isZero (z : Sp.{u} _⦋0⦌) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (nativeCircleEvaluationSquare z) i i.rev) := by
  rw [nativeCircleEvaluationSquare_zeroCorner]
  exact pointZeroVertex.isZero

/-- 元の Sp の各頂点でも、円の評価三角形は実際の普遍評価の生成 loop の比較単体。 -/
lemma nativeCircleEvaluationTriangleFamily_fiber (z : Sp.{u} _⦋0⦌) :
    lift (SSet.const z) (𝟙 (Δ[2] : SSet.{u + 1})) ≫
        nativeCircleEvaluationTriangleFamily =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex
        ((circleEvaluationHomEdge
          (nativeCotensorInput PointedSimplicialSet.circle z).val).edge)) := by
  have hs : lift (SSet.const z) (𝟙 (Δ[2] : SSet.{u + 1})) ≫
      (𝟙 Sp.{u} ⊗ₘ circleParameterTriangle.{u, u + 1}) =
        circleParameterTriangle ≫ lift (SSet.const z) (𝟙 _) := by
    simp only [lift_map, comp_lift, Category.id_comp, Category.comp_id, SSet.comp_const]
  rw [nativeCircleEvaluationTriangleFamily, ← Category.assoc, hs, Category.assoc,
    nativeCotensorEvaluationFamily_fiber, circleParameterTriangle, circleEvaluationHomEdge_edge]
  exact CotensorCompatible.evaluationFiber_parameterTriangle _ _ circleGeneratingEdge

end SerrePositivity.KST.Spectra.OmegaSpectrum
