module

public import SerrePositivity.KST.Spectra.SpectrumZeroGradedFactorization
public import SerrePositivity.KST.Spectra.EnrichedTransformationTriangleStages
public import SerrePositivity.KST.Spectra.SpectrumFunctorZero

/-!
概要：基点での cotensor 評価の零対象経由の因子分解を、実際の coherent な三角形の族にする。
方針：全 Hom の因子分解を三段の豊穣円柱へ送り、nerve と標準二単体の pairing を使う。
規約：中間の図式は定値零図式そのもの。使われ方：loop 四角形の零角の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
local instance zeroTriangleSpectrumSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の零評価の因子分解を保持する、三段の円柱の実際の豊穣関手。 -/
def zeroEvaluationTriangleEnriched (A : PointedSimplicialSet.{u}) :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object (Fin 3) (Object A))
      OmegaSpectrum.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.functor (cotensorEnriched A) (zeroEnriched A) (sourceEnriched A)
    (toZeroEvaluation A) (fromZeroEvaluation A) (parameterEvaluation A A.hom)
    (fun X ↦ (zeroEvaluation_factorization A X).symm)

/-- 零対象経由の因子分解の、全対象・全高次単体で coherent な三角形の族。 -/
def zeroEvaluationTriangleFamily (A : PointedSimplicialSet.{u}) :
    SimplicialNerve (Object A) ⊗ (Δ[2] : SSet.{u + 1}) ⟶ Sp.{u} :=
  EnrichedOrderedCylinder.nerveSimplexFamily 2 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (zeroEvaluationTriangleEnriched A)

/-- 一点スペクトルへの定値豊穣関手の nerve は元の定値零図式そのもの。 -/
lemma zeroEnrichedInfinityMap_eq (A : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (zeroEnriched A) = constantZeroDiagram (SimplicialNerve (Object A)) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  exact (mappingPoint_isTerminal _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint).hom_ext _ _

/-- 因子分解の三角形の最初の頂点図式は元の cotensor 射影。 -/
lemma zeroEvaluationTriangleFamily_zero (A : PointedSimplicialSet.{u}) :
    lift (𝟙 (SimplicialNerve (Object A)))
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 3))) ≫
          zeroEvaluationTriangleFamily A = cotensorInfinityMap A := by
  rw [zeroEvaluationTriangleFamily, ← Category.assoc,
    EnrichedOrderedCylinder.nerveSimplexFamily_vertex, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp,
    zeroEvaluationTriangleEnriched, EnrichedTransformationTriangle.functor_stage_zero]
  rfl

/-- 因子分解の三角形の中間の頂点図式は元の定値零図式。 -/
lemma zeroEvaluationTriangleFamily_one (A : PointedSimplicialSet.{u}) :
    lift (𝟙 (SimplicialNerve (Object A)))
        (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 3))) ≫
          zeroEvaluationTriangleFamily A = constantZeroDiagram (SimplicialNerve (Object A)) := by
  rw [zeroEvaluationTriangleFamily, ← Category.assoc,
    EnrichedOrderedCylinder.nerveSimplexFamily_vertex, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp,
    zeroEvaluationTriangleEnriched, EnrichedTransformationTriangle.functor_stage_one,
    zeroEnrichedInfinityMap_eq]

/-- 因子分解の三角形の最後の頂点図式は元の BF 対象への射影。 -/
lemma zeroEvaluationTriangleFamily_two (A : PointedSimplicialSet.{u}) :
    lift (𝟙 (SimplicialNerve (Object A)))
        (SSet.const (stdSimplex.obj₀Equiv.symm (2 : Fin 3))) ≫
          zeroEvaluationTriangleFamily A = sourceInfinityMap A := by
  rw [zeroEvaluationTriangleFamily, ← Category.assoc,
    EnrichedOrderedCylinder.nerveSimplexFamily_vertex, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp,
    zeroEvaluationTriangleEnriched, EnrichedTransformationTriangle.functor_stage_two]
  rfl

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
