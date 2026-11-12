module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedKernelPerfEquivalence
public import SerrePositivity.KST.NonConnective.DGSuspensionResolvedConnectiveSequence

/-!
概要：同じ各段の I・P から Perf 比較を供給し、元の実構造辺と非連結化対象候補を作る。
方針：実評価 Morita 同値を同じ各段の指定比較欄へ代入し、元の実 Sp 余極限を使う。
規約：段別 I・P・零所属 Z に条件付き。追加 Perf 同値・ν Verdier 認証・Sp 引き戻し性は仮定しない。
使われ方：K-7 c5・d。入力供給の存在、構造射の全入力自然性、非負次数安定化は別工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ) (A : PerfDGInput.{u, max (u + 1) v} R)

/-- 明示の同じ段別 I・P に条件付きで、各段の固定 ν 値への実 Perf 比較を供給する。 -/
def dgSuspensionResolvedPerfEquivalence (n : ℕ) :
    StableModelEquivalence
      (stableCategoryModel (dgKInputStableValue R (dgSuspensionIteration R s A n)))
      (stableCategoryModel (dgKInputStableValue R (dgKappaResolvedKernelKInput R
        (dgSuspensionIteration R s A n) (dgSuspensionIterationStage R s A n).cone))) :=
  dgKappaResolvedKernelPerfEquivalence R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone (dgSuspensionIterationStage R s A n).perfect

variable (Z : ∀ n, DGKappaZeroInput R (dgSuspensionIteration R s A n)
  (dgSuspensionIterationStage R s A n).cone)

/-- 段別 I・P・Z に条件付きで、同じ実評価比較による厳密 BF 列。 -/
def dgSuspensionPerfectConnectiveSequence : SpectrumSequence.{max (u + 1) v} :=
  dgSuspensionResolvedConnectiveSequence R s A Z (dgSuspensionResolvedPerfEquivalence R s A)

/-- 段別 I・P・Z に条件付きで、同じ実列の非連結化対象候補。 -/
def dgSuspensionPerfectConnectiveCandidate : OmegaSpectrum.{max (u + 1) v} :=
  sequentialSpectrum (dgSuspensionPerfectConnectiveSequence R s A Z)

/-- 段別 I・P・Z に条件付きで、同じ実対象候補を頂点とする元の Sp 余錐。 -/
def dgSuspensionPerfectConnectiveCandidateCocone :=
  sequentialCandidateColimitCocone (dgSuspensionPerfectConnectiveSequence R s A Z)

/-- 段別 I・P・Z に条件付きで、同じ実余錐は全写像空間の余極限。 -/
theorem dgSuspensionPerfectConnectiveCandidateCocone_isColimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (dgSuspensionPerfectConnectiveCandidateCocone R s A Z) :=
  sequentialCandidateColimitCocone_isColimit (dgSuspensionPerfectConnectiveSequence R s A Z)

/-- 段別 I・P・Z に条件付きで、元の同じ固定 K(A) から実余極限への零段の脚。 -/
def dgSuspensionPerfectConnectedComparison :
    dgKInputSpectrum R A ⟶ dgSuspensionPerfectConnectiveCandidate R s A Z :=
  dgSuspensionResolvedConnectedComparison R s A Z (dgSuspensionResolvedPerfEquivalence R s A)

end SerrePositivity.KST.NonConnective
