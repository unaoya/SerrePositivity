module
public import SerrePositivity.KST.NonConnective.DGSuspensionIteration
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionRelativeRoofInput
public import SerrePositivity.KST.NonConnective.SequentialIndexFunctors
public import SerrePositivity.KST.NonConnective.SequentialCandidateColimit
public import Mathlib.CategoryTheory.Endomorphism

/-!
概要：指定された各段の実構造辺から、同じ native loop 反復の厳密 BF 列を作る。
方針：Sp の公開 native loop を反復し、元の各辺を厳密 BF 射へ回収する。
規約：元の K 入力からの実構造辺の供給に条件付き。相対屋根の存在・Perf 照合は主張しない。
使われ方：K-7 c5 の形式的部分。元の辺を保つ逐次列を既存の実 Sp 余極限へ渡す。
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
local instance nativeSequenceSimplicialCategory : SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory
local instance nativeSequenceHomKan (X Y : OmegaSpectrum.{w}) : KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex X Y

variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ)
  (A : PerfDGInput.{u, max (u + 1) v} R)

/-- 同じ n 回懸垂の固定 K 頂点に、公開 native loop を同じ n 回だけ作用させる。 -/
def dgSuspensionNativeSequenceVertex (n : ℕ) : Sp.{max (u + 1) v} _⦋0⦌ :=
  ((End.of OmegaSpectrum.nativeLoop ^ n).asHom).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A n)))

variable (β : ∀ n : ℕ,
  SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A n)))
    (OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKInputSpectrum R (dgSuspensionIteration R s A (n + 1))))))

/-- 各段の元の実構造辺の供給に条件付きで、同じ n 回 loop した実辺を保持する。 -/
def dgSuspensionNativeSequenceEdge (n : ℕ) :
    SSet.Edge (dgSuspensionNativeSequenceVertex R s A n)
      (dgSuspensionNativeSequenceVertex R s A (n + 1)) :=
  ((β n).map (End.of OmegaSpectrum.nativeLoop ^ n).asHom).ofEq rfl (by
    simp only [dgSuspensionNativeSequenceVertex, pow_succ, End.mul_asHom]
    rfl)

/-- 明示構造辺に条件付きの、同じ native loop 頂点を表す元の実 BF spectrum。 -/
def dgSuspensionNativeSequenceStage (n : ℕ) : OmegaSpectrum.{max (u + 1) v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (dgSuspensionNativeSequenceVertex R s A n)

/-- 明示構造辺に条件付きで、同じ元の全一単体を表す厳密 BF 遷移射を回収する。 -/
def dgSuspensionNativeSequenceMap (n : ℕ) :
    dgSuspensionNativeSequenceStage R s A n ⟶ dgSuspensionNativeSequenceStage R s A (n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdgeToHom ((dgSuspensionNativeSequenceEdge R s A β n).ofEq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _).symm)

/-- 明示構造辺に条件付きで、回収した BF 遷移射は元の loop 反復辺の全一単体を保つ。 -/
theorem dgSuspensionNativeSequenceMap_edge (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgSuspensionNativeSequenceMap R s A β n)).edge =
      (dgSuspensionNativeSequenceEdge R s A β n).edge := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_hom ((dgSuspensionNativeSequenceEdge R s A β n).ofEq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object _).symm)
  exact congrArg (fun e => e.edge) he

/-- 明示構造辺に条件付きの、同じ元の遷移射を持つ厳密逐次 BF 列。 -/
def dgSuspensionNativeSequence : SpectrumSequence.{max (u + 1) v} :=
  sequentialIndexDown ⋙ Functor.ofSequence (dgSuspensionNativeSequenceMap R s A β)

/-- 明示構造辺に条件付きで、逐次列の隣接射は元の回収 BF 遷移射そのもの。 -/
theorem dgSuspensionNativeSequence_map_succ (n : ℕ) :
    (dgSuspensionNativeSequence R s A β).map
        (homOfLE (X := SequentialIndex.{max (u + 1) v}) (Nat.le_succ n)) =
      dgSuspensionNativeSequenceMap R s A β n := by
  exact Functor.ofSequence_map_homOfLE_succ _ n

/-- 明示構造辺に条件付きの非連結化対象候補。構造辺の供給の存在は主張しない。 -/
def dgSuspensionNativeCandidate : OmegaSpectrum.{max (u + 1) v} :=
  sequentialSpectrum (dgSuspensionNativeSequence R s A β)

/-- 明示構造辺に条件付きで、同じ候補を頂点とする実 Sp 余極限余錐。 -/
def dgSuspensionNativeCandidateCocone :=
  sequentialCandidateColimitCocone (dgSuspensionNativeSequence R s A β)

/-- 明示構造辺に条件付きで、同じ実 Sp 余錐は全写像空間で余極限である。 -/
theorem dgSuspensionNativeCandidateCocone_isColimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (dgSuspensionNativeCandidateCocone R s A β) :=
  sequentialCandidateColimitCocone_isColimit (dgSuspensionNativeSequence R s A β)

end SerrePositivity.KST.NonConnective
