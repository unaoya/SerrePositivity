module

public import SerrePositivity.KST.Spectra.SpectrumZeroTriangleTrace
public import SerrePositivity.KST.Spectra.SpectrumCircleCompositionTraces

/-!
概要：元の Sp 頂点での参照零三角形の Hom 経路が定値であることを厳密に示す。
方針：逆射が選んだ元の整合入力での三角形を回収し、単位を経由する Hom の式を使う。
規約：元の入力と二単体を保持。使われ方：円評価の Hom 正方形の境界の計算。
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
open CoherentPathCoordinates
local instance nativeZeroTraceSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 元の頂点での参照三角形は、元の逆射が選んだ整合入力の同じ三角形。 -/
lemma nativeZeroEvaluationTriangleFamily_fiber (A : PointedSimplicialSet.{u})
    (z : Sp.{u} _⦋0⦌) :
    lift (SSet.const z) (𝟙 (Δ[2] : SSet.{u + 1})) ≫
        nativeZeroEvaluationTriangleFamily A =
      lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (nativeCotensorInput A z))) (𝟙 _) ≫
        CotensorCompatible.zeroEvaluationTriangleFamily A := by
  rw [nativeZeroEvaluationTriangleFamily, ← Category.assoc, lift_map,
    SSet.const_comp, Category.id_comp, nativeCotensorInput_vertex]

/-- 元の参照零三角形の頂点評価は、元の整合入力の参照二単体そのもの。 -/
lemma circleZeroFunctorTriangleAt (z : Sp.{u} _⦋0⦌) :
    SSet.yonedaEquiv (circleZeroFunctorTriangle ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt z) =
      CotensorCompatible.zeroEvaluationTriangleAt PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z) := by
  rw [circleZeroFunctorTriangle, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex,
    nativeZeroEvaluationTriangleFamily_fiber]
  rfl

/-- 元の参照零三角形の移送後の経路は、元の Hom 内の定値経路。 -/
lemma circleEvaluationReferenceTrace_constant (z : Sp.{u} _⦋0⦌) :
    ∃ y, circleEvaluationReferenceTrace z = SSet.const y := by
  have hc := (triangleTrace_constant_congr (circleZeroFunctorTriangleAt z)).mpr
    (CotensorCompatible.zeroEvaluationTriangleTrace_constant PointedSimplicialSet.circle
      (nativeCotensorInput PointedSimplicialSet.circle z))
  obtain ⟨y, hy⟩ := hc
  unfold circleEvaluationReferenceTrace
  erw [hy, SSet.const_comp]
  exact ⟨_, rfl⟩

end SerrePositivity.KST.Spectra.OmegaSpectrum
