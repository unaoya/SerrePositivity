module
public import SerrePositivity.KST.NonConnective.DGKappaUnconditionalConeZero
public import SerrePositivity.KST.NonConnective.DGSuspensionSuppliedBFSequence

/-!
概要：D-8 の実 I・P・Z を、同じ実 BF 四角形による反復列と連結比較へ代入する。
方針：固定 κ の実段供給と各段の実零所属を、採用済みの非負次数 fiber 経路へ渡す。
規約：共終性と一回の未完備 S• fibration は明示引数。全 native 自然性は推論しない。
使われ方：K-7 c5・d3 の独立した段別 I・P・Z を要しない実候補と実 Sp 余極限。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.NonConnective
local instance unconditionalBFSequenceSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ) (A : PerfDGInput.{u, max (u + 1) v} R)
  (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
      (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
        Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))

/-- 概要：同じ実 I・P・Z と BF 四角形から得た各段の固定 K の実構造辺。
方針：同じ無条件段供給を採用済みの実 BF 構造辺へ渡す。
規約：共終性に条件付き。使われ方：元の実非連結化候補の同じ隣接射。 -/
def dgSuspensionUnconditionalBFStructureEdge (n : ℕ) :=
  dgSuspensionSuppliedBFStructureEdge R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A
    hcofinal (dgSuspensionUnconditionalIteration_zeroInput R κ hκ A) n

/-- 概要：I・P・Z の存在引数なしで、同じ実 BF 構造辺を持つ非連結化候補。
方針：同じ実供給 BF 候補へ D の実段入力を代入する。
規約：共終性に条件付き。全入力上の関手性・局所化登録は主張しない。
使われ方：K-7 c5 の対象別の実候補。 -/
def dgSuspensionUnconditionalBFCandidate :=
  dgSuspensionSuppliedBFCandidate R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A
    hcofinal (dgSuspensionUnconditionalIteration_zeroInput R κ hκ A)

/-- 概要：同じ実候補を頂点とする元の Sp 余錐。
方針：同じ実隣接射を持つ採用済み余錐を回収する。
規約：共終性に条件付き。使われ方：群余極限だけでない実 Sp 余極限の保持。 -/
def dgSuspensionUnconditionalBFCandidateCocone :=
  dgSuspensionSuppliedBFCandidateCocone R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A
    hcofinal (dgSuspensionUnconditionalIteration_zeroInput R κ hκ A)

/-- 概要：同じ実 Sp 余錐は全写像空間の余極限。
方針：元の同じ余錐の普遍性を実段供給へ特殊化する。
規約：共終性に条件付き。使われ方：K-7 の対象別実非連結化候補。 -/
theorem dgSuspensionUnconditionalBFCandidateCocone_isColimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (dgSuspensionUnconditionalBFCandidateCocone R κ hκ A hcofinal) :=
  dgSuspensionSuppliedBFCandidateCocone_isColimit R
    (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A hcofinal
    (dgSuspensionUnconditionalIteration_zeroInput R κ hκ A)

/-- 概要：元の連結固定 K(A) から同じ実候補への同じ余錐の零段の脚。
方針：採用済み比較の同じ実射を回収する。
規約：共終性に条件付き。使われ方：K-7 d3 の元の固定 K との連結比較。 -/
def dgSuspensionUnconditionalBFConnectedComparison :=
  dgSuspensionSuppliedBFConnectedComparison R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A
    hcofinal (dgSuspensionUnconditionalIteration_zeroInput R κ hκ A)

variable (hS : ∀ n : ℕ, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare
  ((dgKappaNativeVerdierDiagram R (dgSuspensionUnconditionalIteration R κ hκ A n)
    (dgSuspensionIterationStage R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n).cone).square ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} 0)))
include hS

/-- 概要：実段供給で得た同じ固定 K からの連結比較は非負次数 π 同型。
方針：同じ実 cone の零性と採用済みの非負次数 fiber 比較へ代入する。
規約：共終性と一回の未完備 S• fibration に条件付き。全段の Sp 引き戻し性は取らない。
使われ方：K-7 d3 の段別 I・P・Z の存在仮定を除いた比較。 -/
theorem dgSuspensionUnconditionalBFConnectedComparison_nonnegative (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgSuspensionUnconditionalBFConnectedComparison R κ hκ A hcofinal) j) :=
  dgSuspensionSuppliedBFConnectedComparison_nonnegative R
    (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A hcofinal
    (dgSuspensionUnconditionalIteration_zeroInput R κ hκ A) hS j hj

/-- 概要：同じ実候補の全整数 π を、十分後の同じ実懸垂の固定 K 群へ比較する。
方針：同じ実隣接射を持つ既存の末尾表示へ実段入力を代入する。
規約：共終性・未完備 S• fibration に条件付き。負群の消滅は主張しない。
使われ方：K-7 d3 の元の実候補の全整数群表示。 -/
def dgSuspensionUnconditionalBFCandidate_tailPiEquiv (j : ℤ) (n : ℕ) (hn : (-j).toNat ≤ n) :
    OmegaSpectrum.homotopyGroup
      (dgKInputSpectrum R (dgSuspensionUnconditionalIteration R κ hκ A n)) (j + n) ≃*
      OmegaSpectrum.homotopyGroup (dgSuspensionUnconditionalBFCandidate R κ hκ A hcofinal) j :=
  dgSuspensionSuppliedBFCandidate_tailPiEquiv R
    (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A hcofinal
    (dgSuspensionUnconditionalIteration_zeroInput R κ hκ A) hS j n hn

end SerrePositivity.KST.NonConnective
