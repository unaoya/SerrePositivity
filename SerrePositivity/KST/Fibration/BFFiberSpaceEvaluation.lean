module
public import SerrePositivity.KST.Fibration.RawFiberSpaceEvaluation
public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberConeTransportIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConeReindex
public import SerrePositivity.KST.LocalizingInvariants.BFFiberSquare
public import SerrePositivity.KST.LocalizingInvariants.NativeFiberSequence
public import SerrePositivity.KST.LocalizingInvariants.FiberSquareRelativeComparison

/-! # 元の BF fiber 錐・四角形の、基点忘却後の全 coherent 段評価 -/

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

local instance bfSpaceEvaluationSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y : OmegaSpectrum.{u}}

/-- 元の段ごとの実 fiber 錐を全 coherent 段評価しても、実極限錐である。 -/
theorem rawFiberInfinityCone_spaceEvaluation_isLimit (p : X ⟶ Y)
    [hp : ∀ n, Fibration (p.app n).right] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((FiberModel.infinityCone p).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation n))) := by
  have h := rawFiberSpaceEvaluationCone_isLimit p n
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (spectrumSpaceEvaluation n)).mapCone
      (FiberModel.smallCone p))) at h
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.strictCoherentCone_postcomp] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeCast_isLimit_iff _ _).mp h

/-- 元の BF fiber 頂点への全図式同型を保ったまま、置換後の錐の各段も極限。 -/
theorem replacedFiberCone_spaceEvaluation_isLimit (p : X ⟶ Y)
    [hp : ∀ n, Fibration (p.app n).right] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((FiberModel.replacedCone p).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation n))) :=
  (rawFiberInfinityCone_spaceEvaluation_isLimit p n).of_functorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (FiberModel.replacedConeDiagramIso p).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation n)))

/-- 任意の元の BF 射の homotopy fiber 錐は、全 coherent 段評価で極限錐へ写る。 -/
theorem homotopyFiberCone_spaceEvaluation_isLimit (p : X ⟶ Y) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((FiberModel.homotopyFiberCone p).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation n))) :=
  by
    have h := replacedFiberCone_spaceEvaluation_isLimit
      (OmegaSpectrum.fibrationReplacementProjection p) n
    exact h.of_functorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp
      (FiberModel.homotopyFiberConeTransportIso p).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation n)))

local instance bfSpaceEvaluationNerve : Quasicategory (SimplicialNerve OmegaSpectrum.{u}) :=
  sp_quasicategory

/-- 元の BF fiber 錐の同じ horn 制限は、段評価後にも実極限錐となる。 -/
theorem homotopyFiberHorn_spaceEvaluation_isLimit {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone ((FiberModel.hornCone p).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation n))) := by
  let Q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation n)
  let c := (FiberModel.homotopyFiberCone p).postcomp Q
  let i := CospanShape.strictCospanHornIso.{u, u + 1}.inv
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := homotopyFiberCone_spaceEvaluation_isLimit p n
  have hr := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeRestrict_isLimit_iff c i).mp hc
  apply hr.of_functorIso
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeRestrict c i).val = ((FiberModel.hornCone p).postcomp Q).val := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u + 1})) i ≫
      ((FiberModel.homotopyFiberCone p).val ≫ Q)) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u + 1})) i ≫ (FiberModel.homotopyFiberCone p).val) ≫ Q
    exact (Category.assoc _ _ _).symm
  rw [he]

/-- 元の BF 射の同じ homotopy fiber 四角形は、各実段で ∞ 引き戻しへ写る。 -/
theorem homotopyFiberSquare_spaceEvaluation_isPullback {X Y : OmegaSpectrum.{u}}
    (p : X ⟶ Y) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((FiberModel.homotopyFiberSquare p).square ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation n)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coneSquare_isPullback _ (homotopyFiberHorn_spaceEvaluation_isLimit p n)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫
    ((FiberModel.hornCone p).val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation n))) at h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.inv ≫ (FiberModel.hornCone p).val) ≫ _)
  rw [Category.assoc]
  exact h

/-- 任意の元の Sp fiber 四角形は、同じ全 coherent 段評価で引き戻しへ写る。 -/
theorem spectrumFiberSquare_spaceEvaluation_isPullback (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle Sp.{u})
    (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence t) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (t.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation n)) := by
  let p := NativeFiber.rightMap t
  let s := NativeFiber.asFiberSquare t ht
  let e := (FiberComparison.relativeFunctorIso s (FiberModel.homotopyFiberSquare p)).iso
  exact (homotopyFiberSquare_spaceEvaluation_isPullback p n).of_functorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (spectrumSpaceEvaluation n)))

end SerrePositivity.KST.Fibration
