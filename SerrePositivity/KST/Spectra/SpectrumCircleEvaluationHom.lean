module

public import SerrePositivity.KST.Spectra.SpectrumCotensorEvaluationFiber
public import SerrePositivity.KST.Spectra.CircleParameterTriangle

/-!
概要：円の評価三角形を、元の BF 写像空間の普遍評価の一単体へ厳密に同定する。
方針：coherent Hom 比較の後合成自然性と、一対象上の評価円柱の全 Hom の式を使う。
規約：三角形の元の単体を保持する。使われ方：評価四角形の表現可能な比較の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleEvaluationHomSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
namespace CotensorCompatible

/-- パラメータの辺の三角形を一対象で評価すると、元の普遍評価の Hom 比較単体になる。 -/
lemma evaluationFiber_parameterTriangle (A : PointedSimplicialSet.{u}) (X : Object A)
    {x y : A.right _⦋0⦌} (e : A.right.Edge x y) :
    EnrichedParameterCylinder.parameterTriangle e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (evaluationFiberEnriched A X) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex
        ((cotensorEvaluation A X.val).right.app (Opposite.op ⦋1⦌) e.edge)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, EnrichedParameterCylinder.parameterTriangle,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change (EnrichedParameterCylinder.parameterCompStruct e).simplex.comp SSet
    (evaluationFiberEnriched A X) = _
  rw [EnrichedParameterCylinder.parameterCompStruct_simplex, evaluationFiber_comparison]

/-- 共通解像上でも、元のパラメータ辺の全三角形が同じ普遍評価の単体を保持する。 -/
lemma evaluationNerveFamily_parameterTriangle_fiber (A : PointedSimplicialSet.{u}) (X : Object A)
    {x y : A.right _⦋0⦌} (e : A.right.Edge x y) :
    EnrichedParameterCylinder.parameterTriangle e ≫
      lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)) (𝟙 _) ≫ evaluationNerveFamily A =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex
          ((cotensorEvaluation A X.val).right.app (Opposite.op ⦋1⦌) e.edge)) := by
  rw [evaluationNerveFamily_fiber, evaluationFiber_parameterTriangle]

/-- 円の生成辺の評価三角形は、元の普遍評価の生成 loop の coherent な単体そのもの。 -/
lemma circleEvaluationNerveFamily_fiber (X : Object PointedSimplicialSet.circle.{u}) :
    circleParameterTriangle.{u, u + 1} ≫
      lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)) (𝟙 _) ≫
        evaluationNerveFamily PointedSimplicialSet.circle =
          SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex
            ((cotensorEvaluation PointedSimplicialSet.circle X.val).right.app
              (Opposite.op ⦋1⦌) circleGeneratingEdge.edge)) :=
  evaluationNerveFamily_parameterTriangle_fiber _ X circleGeneratingEdge

end CotensorCompatible

/-- 円の普遍評価の基点での値は、元の BF 写像空間の零写像の頂点。 -/
lemma circleEvaluationHom_basepoint (X : OmegaSpectrum.{u}) :
    (cotensorEvaluation PointedSimplicialSet.circle X).right.app (Opposite.op ⦋0⦌)
        circleBasepoint =
      (RawSpectrumMapping.pointedSpace (cotensor PointedSimplicialSet.circle X)
        X.toKanSequence).hom.app (Opposite.op ⦋0⦌) PUnit.unit := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (Under.w (cotensorEvaluation PointedSimplicialSet.circle X))
      (Opposite.op ⦋0⦌)) PUnit.unit
  exact h

/-- 円の生成辺の普遍評価は、実際の BF 写像空間内で零写像に基づく loop。 -/
def circleEvaluationHomEdge (X : OmegaSpectrum.{u}) :
    (RawSpectrumMapping.pointedSpace (cotensor PointedSimplicialSet.circle X)
      X.toKanSequence).right.Edge
        ((RawSpectrumMapping.pointedSpace (cotensor PointedSimplicialSet.circle X)
          X.toKanSequence).hom.app (Opposite.op ⦋0⦌) PUnit.unit)
        ((RawSpectrumMapping.pointedSpace (cotensor PointedSimplicialSet.circle X)
          X.toKanSequence).hom.app (Opposite.op ⦋0⦌) PUnit.unit) :=
  (circleGeneratingEdge.map (cotensorEvaluation PointedSimplicialSet.circle X).right).ofEq
    (circleEvaluationHom_basepoint X) (circleEvaluationHom_basepoint X)

/-- 普遍評価の loop の一単体は、円の元の生成一単体の評価そのもの。 -/
lemma circleEvaluationHomEdge_edge (X : OmegaSpectrum.{u}) :
    (circleEvaluationHomEdge X).edge =
      (cotensorEvaluation PointedSimplicialSet.circle X).right.app (Opposite.op ⦋1⦌)
        circleGeneratingEdge.edge := rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum
