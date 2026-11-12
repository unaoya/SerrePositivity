module
public import SerrePositivity.KST.NonConnective.DGSuspensionUnconditionalBFSequence

/-!
概要：D-8 の同じ実反復で、連結 SOA 比較と全整数末尾表示の隣接射整合を保持する。
方針：同じ実 I・P・Z を、採用済み比較の自然性へ代入する。
規約：共終性・未完備 S• fibration は明示入力。全 native 作用の供給は主張しない。
使われ方：K-7 d3 の実連結比較と末尾表示を同じ構造辺に照合する。
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
local instance unconditionalBFComparisonSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ) (A : PerfDGInput.{u, max (u + 1) v} R)
  (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
      (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
        Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))

/-- 概要：同じ連結 SOA K から同じ実 BF 候補への元の比較射。
方針：元の SOA 比較と同じ実余錐の零段の脚を回収する。
規約：共終性に条件付き。使われ方：元の連結 K 模型との照合。 -/
def dgSuspensionUnconditionalBFSOAComparison :=
  dgSuspensionSuppliedBFSOAComparison R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A
    hcofinal (dgSuspensionUnconditionalIteration_zeroInput R κ hκ A)

variable (hS : ∀ n : ℕ, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare
  ((dgKappaNativeVerdierDiagram R (dgSuspensionUnconditionalIteration R κ hκ A n)
    (dgSuspensionIterationStage R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n).cone).square ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor.{max (u + 1) v} 0)))
include hS

/-- 概要：同じ実反復の連結 SOA 比較も非負次数 π 同型。
方針：同じ実段入力と一回の未完備 S• 比較を既存定理へ代入する。
規約：共終性・hS に条件付き。全段の Sp 引き戻し性は仮定しない。
使われ方：K-7 d3 の元の連結 SOA K との比較。 -/
theorem dgSuspensionUnconditionalBFSOAComparison_nonnegative (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgSuspensionUnconditionalBFSOAComparison R κ hκ A hcofinal) j) :=
  dgSuspensionSuppliedBFSOAComparison_nonnegative R
    (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A hcofinal
    (dgSuspensionUnconditionalIteration_zeroInput R κ hκ A) hS j hj

set_option maxRecDepth 4096 in
/-- 概要：同じ全整数末尾表示は元の隣接構造射を通っても同じ余錐の脚となる。
方針：同じ実構造辺を持つ既存の末尾表示の自然性へ実段供給を代入する。
規約：共終性・hS に条件付き。深さの増加は同じ依存型の反復照合に限る。
使われ方：K-7 d3 の全整数表示と実反復列の整合。 -/
theorem dgSuspensionUnconditionalBFCandidate_tailPiEquiv_succ
    (j : ℤ) (n : ℕ) (hn : (-j).toNat ≤ n)
    (x : OmegaSpectrum.homotopyGroup
      (dgKInputSpectrum R (dgSuspensionUnconditionalIteration R κ hκ A n)) (j + n)) :
    dgSuspensionUnconditionalBFCandidate_tailPiEquiv R κ hκ A hcofinal hS j (n + 1)
        (Nat.le_succ_of_le hn)
        (dgSuspensionShiftedTransition R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A
          (dgSuspensionUnconditionalBFStructureEdge R κ hκ A hcofinal) n j x) =
      dgSuspensionUnconditionalBFCandidate_tailPiEquiv R κ hκ A hcofinal hS j n hn x :=
  dgSuspensionSuppliedBFCandidate_tailPiEquiv_succ R
    (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A hcofinal
    (dgSuspensionUnconditionalIteration_zeroInput R κ hκ A) hS j n hn x

end SerrePositivity.KST.NonConnective
