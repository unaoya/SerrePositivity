module
public import SerrePositivity.KST.Fibration.RawFiberKanEvaluation
public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeTransportIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConeReindex

/-! # 元の BF fiber 錐は、同じ全 coherent 段評価で極限錐へ写る -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories

open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration

local instance bfEvaluationSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y : OmegaSpectrum.{u}}

/-- 元の段ごとの実 fiber 錐を全 coherent 段評価しても、実極限錐である。 -/
theorem rawFiberInfinityCone_evaluation_isLimit (p : X ⟶ Y)
    [hp : ∀ n, Fibration (p.app n).right] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((FiberModel.infinityCone p).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation n))) := by
  have h := rawFiberKanEvaluationCone_isLimit p n
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (spectrumKanEvaluation n)).mapCone
      (FiberModel.smallCone p))) at h
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.strictCoherentCone_postcomp] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeCast_isLimit_iff _ _).mp h

/-- 元の BF fiber 頂点への全図式同型を保ったまま、置換後の錐の各段も極限。 -/
theorem replacedFiberCone_evaluation_isLimit (p : X ⟶ Y)
    [hp : ∀ n, Fibration (p.app n).right] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((FiberModel.replacedCone p).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation n))) :=
  (rawFiberInfinityCone_evaluation_isLimit p n).of_functorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (FiberModel.replacedConeDiagramIso p).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation n)))

/-- 任意の元の BF 射の homotopy fiber 錐は、全 coherent 段評価で極限錐へ写る。 -/
theorem homotopyFiberCone_evaluation_isLimit (p : X ⟶ Y) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((FiberModel.homotopyFiberCone p).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation n))) :=
  by
    have h := replacedFiberCone_evaluation_isLimit
      (OmegaSpectrum.fibrationReplacementProjection p) n
    exact h.of_functorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp
      (FiberModel.homotopyFiberConeTransportIso p).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumKanEvaluation n)))

end SerrePositivity.KST.Fibration
