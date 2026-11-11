module

public import SerrePositivity.KST.Spectra.D3ComparisonResolution
public import SerrePositivity.KST.Spectra.SpectrumLoopTailComparison
public import SerrePositivity.KST.Spectra.RawSpectrumPreWhitehead
public import SerrePositivity.KST.NonConnective.SequentialRelativeHomFibration
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.KanFibrationEquivalence

/-!
概要：既存の実 delooping 射を相対 BF 分解し、実 loop 頂点へ写る BF 始点を作る。
方針：元の射への相対分解と、その左因子による全 Raw Hom の自明 fibration を使う。
規約：対象別の構成。選択した射の全 Hom 自然性・loop 図式族は後続工程。
使われ方：d3b② の L_X と a_X、および補助単位を延長するための実充填。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.NonConnective
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance nativeSourceSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 実 delooping 比較を分解して得る、元の X を含む BF 始点。 -/
def loopSource (X : OmegaSpectrum.{u}) : OmegaSpectrum.{u} :=
  sequentialBFArrowMiddle (deloopingComparison X)

/-- 元の X から同じ BF 始点への相対左因子。 -/
def loopSourceInclusion (X : OmegaSpectrum.{u}) : X ⟶ loopSource X :=
  sequentialBFArrowLeft (deloopingComparison X)

/-- BF 始点から厳密 tail 終点の実 loop 頂点への元の右因子。 -/
def loopSourceToBasedLoop (X : OmegaSpectrum.{u}) : loopSource X ⟶ BasedLoop.obj (tail X) :=
  sequentialBFArrowRight (deloopingComparison X)

/-- 両因子の合成は選び直した同値ではなく、元の delooping 射自体。 -/
@[reassoc]
lemma loopSource_fac (X : OmegaSpectrum.{u}) :
    loopSourceInclusion X ≫ loopSourceToBasedLoop X = deloopingComparison X :=
  sequentialBFArrow_fac (deloopingComparison X)

/-- 同じ左因子の零段・全相対 latching 射は実際に単射。 -/
lemma loopSourceInclusion_relative (X : OmegaSpectrum.{u}) :
    IsSequentialRelativeCofibration (loopSourceInclusion X) :=
  sequentialBFArrowLeft_isRelativeCofibration (deloopingComparison X)

/-- 同じ右因子は全段で全単射に対する RLP を持つ。 -/
lemma loopSourceToBasedLoop_rlp (X : OmegaSpectrum.{u}) (n : ℕ) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      ((loopSourceToBasedLoop X).app n).right :=
  sequentialBFArrowRight_rlp (deloopingComparison X) n

/-- 同じ左因子は零次数を含む各段の全基点 π 同型。 -/
lemma loopSourceInclusion_levelwise (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((loopSourceInclusion X).app n).right := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := ((loopSourceToBasedLoop X).app n).right) _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (loopSourceToBasedLoop_rlp X n))
  rw [← Under.comp_right]
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((loopSourceInclusion X ≫ loopSourceToBasedLoop X).app n).right
  rw [loopSource_fac]
  exact deloopingComparison_levelwise X n

/-- 実 loop 頂点への指定右因子自身が元の Sp の可逆辺。 -/
lemma loopSourceToBasedLoop_isInvertible (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (loopSourceToBasedLoop X)) :=
  SpectrumMappingAcyclic.isInvertible_of_levelwise _
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ (loopSourceToBasedLoop_rlp X n))

/-- 同じ BF 始点と厳密 tail 終点の実 loop 四角形の始点との指定同型。 -/
def loopSourceBasedLoopVertexIso (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (loopSource X)) (BasedLoop.square (tail X)).vertex := by
  rw [BasedLoop.square_vertex]
  haveI := loopSourceToBasedLoop_isInvertible X
  exact asIso (SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (loopSourceToBasedLoop X)))

/-- nativeLoop 正本の同じ終点での値と BF 始点を点ごとに比較する。 -/
def loopSourceNativeVertexIso (X : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (nativeLoop.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (tail X)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (loopSource X)) :=
  nativeLoopVertexIso (BasedLoop.square (tail X)) ≪≫ (loopSourceBasedLoopVertexIso X).symm

/-- 左因子の前合成は任意の Kan 列への元の全 Hom で実自明 Kan fibration。 -/
lemma loopSourcePre_trivialKanFibration (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (RawSpectrumMapping.pre (loopSourceInclusion X) Y) := by
  let := sequentialRawHomPre_fibration (loopSourceInclusion X) (loopSourceInclusion_relative X) Y
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.trivialKanFibration_of_fibration_of_simplicialHomotopyEquivalence _
    (RawSpectrumMapping.pre_homotopyEquivalence_of_levelwise
      (loopSourceInclusion X) (loopSourceInclusion_levelwise X) Y)

/-- 任意の部分パラメータに固定した比較を保ち、同じ左因子に沿って全 Hom を延長する。 -/
lemma exists_relative_loopSourceFamily (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    {V U : SSet.{u}} (j : V ⟶ U) [Mono j]
    (a : V ⟶ RawSpectrumMapping.space (loopSource X) Y)
    (b : U ⟶ RawSpectrumMapping.space X Y)
    (h : a ≫ RawSpectrumMapping.pre (loopSourceInclusion X) Y = j ≫ b) :
    ∃ c : U ⟶ RawSpectrumMapping.space (loopSource X) Y,
      j ≫ c = a ∧ c ≫ RawSpectrumMapping.pre (loopSourceInclusion X) Y = b := by
  let := loopSourcePre_trivialKanFibration X Y
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := RawSpectrumMapping.pre (loopSourceInclusion X) Y)
    j inferInstance
  let sq : CommSq a j (RawSpectrumMapping.pre (loopSourceInclusion X) Y) b := ⟨h⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
