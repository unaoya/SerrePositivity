module
public import SerrePositivity.KST.Fibration.BFFiberKanEvaluation
public import SerrePositivity.KST.LocalizingInvariants.BFFiberSquare
public import SerrePositivity.KST.LocalizingInvariants.NativeFiberSequence
public import SerrePositivity.KST.LocalizingInvariants.FiberSquareRelativeComparison

/-! # 元の Sp fiber 四角形は、全 coherent 段評価で引き戻しへ写る -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration

local instance fiberSquareEvaluationSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance fiberSquareEvaluationNerve : Quasicategory (SimplicialNerve OmegaSpectrum.{u}) :=
  sp_quasicategory

/-- 元の BF fiber 錐の同じ horn 制限は、段評価後にも実極限錐となる。 -/
theorem homotopyFiberHorn_evaluation_isLimit {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y) (n : ℕ) :
    IsLimitCone ((FiberModel.hornCone p).postcomp
      (coherentNerveMap (spectrumKanEvaluation n))) := by
  let Q := coherentNerveMap (spectrumKanEvaluation n)
  let c := (FiberModel.homotopyFiberCone p).postcomp Q
  let i := CospanShape.strictCospanHornIso.{u, u + 1}.inv
  have hc : IsLimitCone c := homotopyFiberCone_evaluation_isLimit p n
  have hr := (coherentConeRestrict_isLimit_iff c i).mp hc
  apply hr.of_functorIso
  have he : (coherentConeRestrict c i).val = ((FiberModel.hornCone p).postcomp Q).val := by
    change (joinMap (𝟙 (Δ[0] : SSet.{u + 1})) i ≫
      ((FiberModel.homotopyFiberCone p).val ≫ Q)) =
        (joinMap (𝟙 (Δ[0] : SSet.{u + 1})) i ≫ (FiberModel.homotopyFiberCone p).val) ≫ Q
    exact (Category.assoc _ _ _).symm
  rw [he]

/-- 元の BF 射の同じ homotopy fiber 四角形は、各実段で ∞ 引き戻しへ写る。 -/
theorem homotopyFiberSquare_evaluation_isPullback {X Y : OmegaSpectrum.{u}}
    (p : X ⟶ Y) (n : ℕ) :
    IsPullbackSquare ((FiberModel.homotopyFiberSquare p).square ≫
      coherentNerveMap (spectrumKanEvaluation n)) := by
  have h := coneSquare_isPullback _ (homotopyFiberHorn_evaluation_isLimit p n)
  change IsPullbackSquare (cospanConeSquareIso.inv ≫
    ((FiberModel.hornCone p).val ≫ coherentNerveMap (spectrumKanEvaluation n))) at h
  change IsPullbackSquare ((cospanConeSquareIso.inv ≫ (FiberModel.hornCone p).val) ≫ _)
  rw [Category.assoc]
  exact h

/-- 任意の元の Sp fiber 四角形は、同じ全 coherent 段評価で引き戻しへ写る。 -/
theorem spectrumFiberSquare_evaluation_isPullback (t : ZeroTriangle Sp.{u})
    (ht : IsFiberSequence t) (n : ℕ) :
    IsPullbackSquare (t.square ≫ coherentNerveMap (spectrumKanEvaluation n)) := by
  let p := NativeFiber.rightMap t
  let s := NativeFiber.asFiberSquare t ht
  let e := (FiberComparison.relativeFunctorIso s (FiberModel.homotopyFiberSquare p)).iso
  exact (homotopyFiberSquare_evaluation_isPullback p n).of_functorIso
    (FunctorIso.postcomp e.symm (coherentNerveMap (spectrumKanEvaluation n)))

end SerrePositivity.KST.Fibration
