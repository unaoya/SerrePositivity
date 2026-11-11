module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionKernelKComparison
public import SerrePositivity.KST.NonConnective.DGSuspensionNativeSequence

/-!
概要：各反復段の実相対屋根と指定 Perf 同値から、同じ構造射の実 Sp 余極限を作る。
方針：元の固定 K の始点へ戻した実構造射を native loop 反復列へ渡す。
規約：段別 I・P、実相対屋根、零所属、指定全関手 Perf 同値に条件付き。存在や P との照合は主張しない。
使われ方：K-7 c5 の形式的部分。全段で元の商と実構造辺を保持する。
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
local instance relativeRoofSequenceSimplicialCategory : SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory
local instance relativeRoofSequenceHomKan (X Y : OmegaSpectrum.{w}) : KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex X Y

variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ)
  (A : PerfDGInput.{u, max (u + 1) v} R)
  (ρ : ∀ n, DGKappaSuspensionRelativeRoofInput R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone)
  (Z : ∀ n, DGKappaZeroInput R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone)
  (e : ∀ n, StableModelEquivalence
    (stableCategoryModel (dgKInputStableValue R (dgSuspensionIteration R s A n)))
    (stableCategoryModel (dgKInputStableValue R (ρ n).kernel)))

/-- 明示した各段の屋根と Perf 同値に条件付きの、元の固定 K からの同じ実構造辺。 -/
def dgSuspensionRelativeRoofStructureEdge (n : ℕ) :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A n)))
      (OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A (n + 1))))) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaSuspensionOriginalStructureMap R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone (ρ n) (e n) (Z n))).ofEq rfl
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _)

/-- 明示した各段の屋根と Perf 同値に条件付きの、同じ実構造射を持つ厳密 BF 列。 -/
def dgSuspensionRelativeRoofSequence : SpectrumSequence.{max (u + 1) v} :=
  dgSuspensionNativeSequence R s A (dgSuspensionRelativeRoofStructureEdge R s A ρ Z e)

/-- 明示した各段の屋根と Perf 同値に条件付きで、同じ列の隣接辺は元の loop 反復辺。 -/
theorem dgSuspensionRelativeRoofSequence_map_succ_edge (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((dgSuspensionRelativeRoofSequence R s A ρ Z e).map
      (homOfLE (X := SequentialIndex.{max (u + 1) v}) (Nat.le_succ n)))).edge =
        (dgSuspensionNativeSequenceEdge R s A
          (dgSuspensionRelativeRoofStructureEdge R s A ρ Z e) n).edge := by
  rw [dgSuspensionRelativeRoofSequence, dgSuspensionNativeSequence_map_succ]
  exact dgSuspensionNativeSequenceMap_edge R s A _ n

/-- 明示した各段の屋根と Perf 同値に条件付きの、同じ列の実 BF 非連結化候補。 -/
def dgSuspensionRelativeRoofCandidate : OmegaSpectrum.{max (u + 1) v} :=
  sequentialSpectrum (dgSuspensionRelativeRoofSequence R s A ρ Z e)

/-- 明示した各段の屋根と Perf 同値に条件付きの、同じ候補を頂点とする実 Sp 余錐。 -/
def dgSuspensionRelativeRoofCandidateCocone :=
  sequentialCandidateColimitCocone (dgSuspensionRelativeRoofSequence R s A ρ Z e)

/-- 明示した各段の屋根と Perf 同値に条件付きで、元の実 Sp 余錐は全写像空間で余極限。 -/
theorem dgSuspensionRelativeRoofCandidateCocone_isColimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (dgSuspensionRelativeRoofCandidateCocone R s A ρ Z e) :=
  sequentialCandidateColimitCocone_isColimit (dgSuspensionRelativeRoofSequence R s A ρ Z e)

/-- 明示した各段の屋根と Perf 同値に条件付きで、同じ余錐の頂点は元の BF 候補。 -/
theorem dgSuspensionRelativeRoofCandidateCocone_vertex :
    (dgSuspensionRelativeRoofCandidateCocone R s A ρ Z e).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgSuspensionRelativeRoofCandidate R s A ρ Z e) :=
  sequentialCandidateColimitCocone_vertex (dgSuspensionRelativeRoofSequence R s A ρ Z e)

end SerrePositivity.KST.NonConnective
