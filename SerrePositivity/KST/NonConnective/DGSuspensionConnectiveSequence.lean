module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedConnectiveMap
public import SerrePositivity.KST.NonConnective.DGSuspensionNativeSequence

/-!
概要：同じ実核・平坦懸垂の連結版構造射から、元の BF 候補上の実 Sp 余極限を作る。
方針：ν の Verdier 認証なしで作った元の実構造辺を、同じ native loop 反復列へ渡す。
規約：段別 I・P、零所属、指定 Perf 同値、実零角の Perf 零性に条件付き。Sp 引き戻し性は使わない。
使われ方：K-7 c5 の一般経路。存在・P 照合・全入力自然性と非負次数安定化は別の工程。
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
local instance connectiveSequenceSimplicialCategory : SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory
local instance connectiveSequenceHomKan (X Y : OmegaSpectrum.{w}) : KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex X Y

variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ)
  (A : PerfDGInput.{u, max (u + 1) v} R)
  (Z : ∀ n, DGKappaZeroInput R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone)
  (e : ∀ n, StableModelEquivalence
    (stableCategoryModel (dgKInputStableValue R (dgSuspensionIteration R s A n)))
    (stableCategoryModel (dgKInputStableValue R (dgKappaResolvedKernelKInput R
      (dgSuspensionIteration R s A n) (dgSuspensionIterationStage R s A n).cone))))
  (hz : ∀ n, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (dgKInputStableValue R
    (LocalizingInvariants.dgFixedNullInput R (dgKappaResolvedKernelKInput R
      (dgSuspensionIteration R s A n) (dgSuspensionIterationStage R s A n).cone))))

/-- 各段の指定 Perf 同値・零所属・実零角に条件付きの、元の固定 K からの同じ実構造辺。 -/
def dgSuspensionConnectiveStructureEdge (n : ℕ) :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A n)))
      (OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A (n + 1))))) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaResolvedConnectiveStructureMap R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone (e n) (Z n) (hz n))).ofEq rfl
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _)

/-- 各段の指定 Perf 同値・零所属・実零角に条件付きの、同じ実構造射を持つ厳密 BF 列。 -/
def dgSuspensionConnectiveSequence : SpectrumSequence.{max (u + 1) v} :=
  dgSuspensionNativeSequence R s A (dgSuspensionConnectiveStructureEdge R s A Z e hz)

/-- 各段の指定 Perf 同値・零所属・実零角に条件付きで、同じ列の隣接辺は元の loop 反復辺。 -/
theorem dgSuspensionConnectiveSequence_map_succ_edge (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((dgSuspensionConnectiveSequence R s A Z e hz).map
      (homOfLE (X := SequentialIndex.{max (u + 1) v}) (Nat.le_succ n)))).edge =
        (dgSuspensionNativeSequenceEdge R s A
          (dgSuspensionConnectiveStructureEdge R s A Z e hz) n).edge := by
  rw [dgSuspensionConnectiveSequence, dgSuspensionNativeSequence_map_succ]
  exact dgSuspensionNativeSequenceMap_edge R s A _ n

/-- 各段の指定 Perf 同値・零所属・実零角に条件付きの、同じ列の実 BF 非連結化候補。 -/
def dgSuspensionConnectiveCandidate : OmegaSpectrum.{max (u + 1) v} :=
  sequentialSpectrum (dgSuspensionConnectiveSequence R s A Z e hz)

/-- 各段の指定 Perf 同値・零所属・実零角に条件付きの、同じ候補を頂点とする実 Sp 余錐。 -/
def dgSuspensionConnectiveCandidateCocone :=
  sequentialCandidateColimitCocone (dgSuspensionConnectiveSequence R s A Z e hz)

/-- 各段の指定 Perf 同値・零所属・実零角に条件付きで、元の実 Sp 余錐は全写像空間で余極限。 -/
theorem dgSuspensionConnectiveCandidateCocone_isColimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (dgSuspensionConnectiveCandidateCocone R s A Z e hz) :=
  sequentialCandidateColimitCocone_isColimit (dgSuspensionConnectiveSequence R s A Z e hz)

/-- 各段の指定 Perf 同値・零所属・実零角に条件付きで、同じ余錐の頂点は元の BF 候補。 -/
theorem dgSuspensionConnectiveCandidateCocone_vertex :
    (dgSuspensionConnectiveCandidateCocone R s A Z e hz).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgSuspensionConnectiveCandidate R s A Z e hz) :=
  sequentialCandidateColimitCocone_vertex (dgSuspensionConnectiveSequence R s A Z e hz)

end SerrePositivity.KST.NonConnective
