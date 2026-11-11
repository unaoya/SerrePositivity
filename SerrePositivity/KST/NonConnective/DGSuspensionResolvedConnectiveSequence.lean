module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedNullPerf
public import SerrePositivity.KST.NonConnective.DGSuspensionConnectiveSequence
public import SerrePositivity.KST.NonConnective.DGSuspensionConnectedComparison

/-!
概要：実零角の Perf 零性を供給し、元の実核と構造辺による同じ非連結化候補を構成する。
方針：各段の同じ全対象商の零性を既存構造射へ代入し、同じ実 Sp 余極限の零段の脚を保つ。
規約：段別 I・P・Z と指定 Perf 同値に条件付き。ν の Verdier 認証・零角追加仮定・Sp 引き戻し性は使わない。
使われ方：K-7 c5 と d の一般経路。供給の存在・P 照合・自然性・安定化は未完。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance resolvedSequenceSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
local instance resolvedSequenceSpectrumHomKan (X Y : OmegaSpectrum.{w}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ) (A : PerfDGInput.{u, max (u + 1) v} R)
  (Z : ∀ n, DGKappaZeroInput R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone)
  (e : ∀ n, StableModelEquivalence
    (stableCategoryModel (dgKInputStableValue R (dgSuspensionIteration R s A n)))
    (stableCategoryModel (dgKInputStableValue R (dgKappaResolvedKernelKInput R
      (dgSuspensionIteration R s A n) (dgSuspensionIterationStage R s A n).cone))))

/-- 段別 I・P・Z と指定 Perf 同値に条件付きで、元の実零角を供給した同じ構造辺。 -/
def dgSuspensionResolvedConnectiveStructureEdge (n : ℕ) :=
  dgSuspensionConnectiveStructureEdge R s A Z e
    (fun k => dgKappaResolvedNullPerf_isZero R (dgSuspensionIteration R s A k)
      (dgSuspensionIterationStage R s A k).cone) n

/-- 明示段別供給に条件付きで、元の実構造辺から作る同じ厳密 BF 列。 -/
def dgSuspensionResolvedConnectiveSequence : SpectrumSequence.{max (u + 1) v} :=
  dgSuspensionNativeSequence R s A (dgSuspensionResolvedConnectiveStructureEdge R s A Z e)

/-- 明示段別供給に条件付きで、同じ実 BF 列の非連結化対象候補。 -/
def dgSuspensionResolvedConnectiveCandidate : OmegaSpectrum.{max (u + 1) v} :=
  sequentialSpectrum (dgSuspensionResolvedConnectiveSequence R s A Z e)

/-- 明示段別供給に条件付きで、同じ候補を頂点とする元の実 Sp 余錐。 -/
def dgSuspensionResolvedConnectiveCandidateCocone :=
  sequentialCandidateColimitCocone (dgSuspensionResolvedConnectiveSequence R s A Z e)

/-- 明示段別供給に条件付きで、元の同じ余錐は全写像空間で余極限。 -/
theorem dgSuspensionResolvedConnectiveCandidateCocone_isColimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (dgSuspensionResolvedConnectiveCandidateCocone R s A Z e) :=
  sequentialCandidateColimitCocone_isColimit (dgSuspensionResolvedConnectiveSequence R s A Z e)

/-- 明示段別供給に条件付きで、元の K(A) から同じ実余極限への零段の脚。 -/
def dgSuspensionResolvedConnectedComparison :
    dgKInputSpectrum R A ⟶ dgSuspensionResolvedConnectiveCandidate R s A Z e :=
  dgSuspensionConnectedComparison R s A (dgSuspensionResolvedConnectiveStructureEdge R s A Z e)

/-- 明示段別供給に条件付きで、元の実比較射の全一単体は同じ余極限余錐の零段の脚そのもの。 -/
theorem dgSuspensionResolvedConnectedComparison_edge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgSuspensionResolvedConnectedComparison R s A Z e)).edge =
      (sequentialCandidateColimitLeg (dgSuspensionResolvedConnectiveSequence R s A Z e) ⟨0⟩).edge :=
  dgSuspensionConnectedComparison_edge R s A _

end SerrePositivity.KST.NonConnective
