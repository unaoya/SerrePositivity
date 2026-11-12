module
public import SerrePositivity.KST.NonConnective.DGKappaThomasonCofinality
public import SerrePositivity.KST.NonConnective.DGSuspensionUnconditionalFirstRowComparison

/-!
概要：共終性の実証明を D-8 の同じ実 I・P・Z の BF 列へ代入する。
方針：既存の構造辺・候補・実余錐を同じ共終性証明に特殊化する。
規約：c4・c5 は SingleRelativeComparison として明示入力。D の全作用は推論しない。
使われ方：K-7 d3・e の共終性入力を要しない同じ非連結化候補と連結比較。
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
local instance thomasonSequenceSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ) (A : PerfDGInput.{u, max (u + 1) v} R)

/-- 同じ実反復の構造辺。共終性は仮定でなく正本の実証明を使う。 -/
def dgSuspensionThomasonStructureEdge (n : ℕ) :=
  dgSuspensionUnconditionalBFStructureEdge R κ hκ A dgKThomasonCofinality n

/-- 同じ実 BF 候補へ共終性の実証明を代入した対象値。全入力作用は別の供給境界。 -/
def dgSuspensionThomasonCandidate :=
  dgSuspensionUnconditionalBFCandidate R κ hκ A dgKThomasonCofinality

/-- 同じ候補を頂点とする実 Sp 余錐。 -/
def dgSuspensionThomasonCandidateCocone :=
  dgSuspensionUnconditionalBFCandidateCocone R κ hκ A dgKThomasonCofinality

/-- 共終性の明示仮定なしで、同じ実余錐は全写像空間の余極限。 -/
theorem dgSuspensionThomasonCandidateCocone_isColimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (dgSuspensionThomasonCandidateCocone R κ hκ A) :=
  dgSuspensionUnconditionalBFCandidateCocone_isColimit R κ hκ A dgKThomasonCofinality

/-- 元の固定 K から同じ実余錐の零段の脚による比較射。 -/
def dgSuspensionThomasonConnectedComparison :=
  dgSuspensionUnconditionalBFConnectedComparison R κ hκ A dgKThomasonCofinality

/-- 元の連結 SOA K から同じ実候補への比較射。 -/
def dgSuspensionThomasonSOAComparison :=
  dgSuspensionUnconditionalBFSOAComparison R κ hκ A dgKThomasonCofinality

variable (c : ∀ n : ℕ, Relative.SingleRelativeComparison
  (dgKappaNativeVerdierDiagram R (dgSuspensionUnconditionalIteration R κ hκ A n)
    (dgSuspensionIterationStage R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n).cone))
include c

/-- 概要：単回相対比較から元の固定 K 比較の非負次数 π 同型。
方針：ofFirstRowSimplices の消費先と同じ実 fibration を使う。
規約：c4・c5 は c に保持。共終性は放電済み。
使われ方：K-7 d3 の固定 K との照合。 -/
theorem dgSuspensionThomasonConnectedComparison_nonnegative (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgSuspensionThomasonConnectedComparison R κ hκ A) j) :=
  dgSuspensionUnconditionalBFConnectedComparison_nonnegative R κ hκ A dgKThomasonCofinality
    (fun n => (c n).isPullback _) j hj

/-- 同じ相対比較から、元の SOA K 比較も非負次数 π 同型。 -/
theorem dgSuspensionThomasonSOAComparison_nonnegative (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgSuspensionThomasonSOAComparison R κ hκ A) j) :=
  dgSuspensionUnconditionalBFSOAComparison_nonnegative R κ hκ A dgKThomasonCofinality
    (fun n => (c n).isPullback _) j hj

/-- 同じ候補の全整数 π を十分後の同じ懸垂 K の群で表示する。 -/
def dgSuspensionThomasonCandidate_tailPiEquiv (j : ℤ) (n : ℕ) (hn : (-j).toNat ≤ n) :
    OmegaSpectrum.homotopyGroup
      (dgKInputSpectrum R (dgSuspensionUnconditionalIteration R κ hκ A n)) (j + n) ≃*
      OmegaSpectrum.homotopyGroup (dgSuspensionThomasonCandidate R κ hκ A) j :=
  dgSuspensionUnconditionalBFCandidate_tailPiEquiv R κ hκ A dgKThomasonCofinality
    (fun n => (c n).isPullback _) j n hn

set_option maxRecDepth 4096 in
/-- 全整数末尾表示は元の同じ隣接構造射を通しても一致する。 -/
theorem dgSuspensionThomasonCandidate_tailPiEquiv_succ
    (j : ℤ) (n : ℕ) (hn : (-j).toNat ≤ n)
    (x : OmegaSpectrum.homotopyGroup
      (dgKInputSpectrum R (dgSuspensionUnconditionalIteration R κ hκ A n)) (j + n)) :
    dgSuspensionThomasonCandidate_tailPiEquiv R κ hκ A c j (n + 1)
        (Nat.le_succ_of_le hn)
        (dgSuspensionShiftedTransition R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A
          (dgSuspensionThomasonStructureEdge R κ hκ A) n j x) =
      dgSuspensionThomasonCandidate_tailPiEquiv R κ hκ A c j n hn x :=
  dgSuspensionUnconditionalBFCandidate_tailPiEquiv_succ R κ hκ A dgKThomasonCofinality
    (fun n => (c n).isPullback _) j n hn x

end SerrePositivity.KST.NonConnective
