module

public import SerrePositivity.KST.Spectra.SpectrumCotensorEvaluationCylinder
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderRestriction

/-!
概要：cotensor の coherent な評価のパラメータ制限と基点での零性。
方針：円柱の制限関手と豊穣評価の厳密な比較を使い、基点では点つき射の条件を適用する。
規約：元の評価の全 Hom パラメータを保持する。使われ方：loop 四角形の零辺の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
local instance evaluationRestrictionSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 任意の単体集合のパラメータによる、元の普遍評価の制限。 -/
def parameterEvaluation (A : PointedSimplicialSet.{u}) {K : SSet.{u}} (i : K ⟶ A.right) :
    GradedNatTrans (Center.ofBraidedObj K) (cotensorEnriched A) (sourceEnriched A) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.gradedRestriction i (cotensorEnriched A) (sourceEnriched A)
    (unpointedGradedEvaluation A)

/-- 任意のパラメータ制限を保持する円柱の豊穣評価。 -/
def restrictedCylinderEnriched (A : PointedSimplicialSet.{u}) {K : SSet.{u}}
    (i : K ⟶ A.right) : EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object K (Object A))
      OmegaSpectrum.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.evaluationFunctor K (cotensorEnriched A) (sourceEnriched A)
    (parameterEvaluation A i)

/-- 円柱のパラメータ制限後の評価は元の制限された評価と厳密に一致。 -/
lemma evaluationCylinderEnriched_restriction (A : PointedSimplicialSet.{u})
    {K : SSet.{u}} (i : K ⟶ A.right) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restriction (C := Object A) i).comp SSet
        (evaluationCylinderEnriched A) = restrictedCylinderEnriched A i :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restriction_evaluation i (cotensorEnriched A) (sourceEnriched A)
    (parameterEvaluation A i) (unpointedGradedEvaluation A) (fun _ ↦ rfl)

/-- パラメータ制限は coherent nerve 上でも元の評価図式と厳密に可換。 -/
lemma evaluationCylinderInfinityMap_restriction (A : PointedSimplicialSet.{u})
    {K : SSet.{u}} (i : K ⟶ A.right) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restriction (C := Object A) i) ≫
        evaluationCylinderInfinityMap A = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (restrictedCylinderEnriched A i) := by
  rw [evaluationCylinderInfinityMap, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp,
    evaluationCylinderEnriched_restriction]

/-- 評価の基点パラメータは、全対象で元の零写像の基点そのもの。 -/
lemma parameterEvaluation_basepoint (A : PointedSimplicialSet.{u}) (X : Object A) :
    (parameterEvaluation A A.hom).app X =
      (RawSpectrumMapping.pointedSpace (cotensor A X.val) X.val.toKanSequence).hom :=
  Under.w (cotensorEvaluation A X.val)

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
