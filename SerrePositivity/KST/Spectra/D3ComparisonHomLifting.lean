module

public import SerrePositivity.KST.Spectra.D3LoopSourceComparison
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeInternalHomTrivialFibration

/-!
概要：異なる X,Y の比較 Hom に、指定左右境界と区間の全端点を保つ相対充填を与える。
方針：a_X と q_Y の元の corner に、区間境界の相対内部 Hom を適用する。
規約：動く対象間の合成に使う充填射自体を構成する。豊穣合成との接続は後続工程。
使われ方：d3b② の c_X と全 Hom の自然性を、二境界固定の比較で構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- X 側の実 loop 左因子と Y 側の実 BF 右射影を保つ元の比較 Hom corner。 -/
abbrev loopComparisonHomCorner (X Y : OmegaSpectrum.{u}) :=
  comparisonCorner Y (loopSourceInclusion X)

/-- 異なる二対象の比較 Hom corner は実際に全単射 RLP を持つ。 -/
instance loopComparisonHomCorner_trivialKanFibration (X Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (loopComparisonHomCorner X Y) :=
  comparisonCorner_trivialKanFibration Y (loopSourceInclusion X) (loopSourceInclusion_relative X)

/-- 全 n 次元の比較境界と、同じ全左右境界を同時に記憶する相対内部 Hom。 -/
def loopComparisonBoundaryCornerSquare (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    internalHom.PullbackObjObj (boundary n).ι (loopComparisonHomCorner X Y) :=
  Functor.PullbackObjObj.ofHasPullback internalHom (boundary n).ι (loopComparisonHomCorner X Y)

/-- 指定単体境界と元の左右境界を同時に固定する比較射。 -/
def loopComparisonBoundaryCorner (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    (ihom (Δ[n] : SSet.{u})).obj
      (RawSpectrumMapping.space (loopSource X) (middle Y).toKanSequence) ⟶
      (loopComparisonBoundaryCornerSquare X Y n).pt :=
  (loopComparisonBoundaryCornerSquare X Y n).π

/-- 比較 Hom の全単体境界を固定しても、全パラメータの単射に対する RLP がある。 -/
instance loopComparisonBoundaryCorner_trivialKanFibration
    (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (loopComparisonBoundaryCorner X Y n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.trivialKanFibration_pullbackObjObjπ (boundary n).ι (loopComparisonHomCorner X Y)
    (loopComparisonBoundaryCornerSquare X Y n)

/-- 元の部分パラメータを保つ比較 n 単体の延長。n=1 は全 Hom の自然性の相対比較。 -/
lemma exists_relative_loopComparisonBoundary (X Y : OmegaSpectrum.{u}) (n : ℕ)
    {V U : SSet.{u}} (j : V ⟶ U) [Mono j]
    (a : V ⟶ (ihom (Δ[n] : SSet.{u})).obj
      (RawSpectrumMapping.space (loopSource X) (middle Y).toKanSequence))
    (b : U ⟶ (loopComparisonBoundaryCornerSquare X Y n).pt)
    (h : a ≫ loopComparisonBoundaryCorner X Y n = j ≫ b) :
    ∃ d : U ⟶ (ihom (Δ[n] : SSet.{u})).obj
        (RawSpectrumMapping.space (loopSource X) (middle Y).toKanSequence),
      j ≫ d = a ∧
      d ≫ (pre (boundary n).ι).app _ = b ≫ (loopComparisonBoundaryCornerSquare X Y n).fst ∧
      d ≫ (ihom (Δ[n] : SSet.{u})).map (loopComparisonHomCorner X Y) =
        b ≫ (loopComparisonBoundaryCornerSquare X Y n).snd := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := loopComparisonBoundaryCorner X Y n) j inferInstance
  let sq : CommSq a j (loopComparisonBoundaryCorner X Y n) b := ⟨h⟩
  refine ⟨sq.lift, sq.fac_left, ?_, ?_⟩
  · have hf := congrArg (· ≫ (loopComparisonBoundaryCornerSquare X Y n).fst) sq.fac_right
    simp only [Category.assoc, loopComparisonBoundaryCorner, Functor.PullbackObjObj.π_fst] at hf
    exact hf
  · have hf := congrArg (· ≫ (loopComparisonBoundaryCornerSquare X Y n).snd) sq.fac_right
    simp only [Category.assoc, loopComparisonBoundaryCorner, Functor.PullbackObjObj.π_snd] at hf
    exact hf

/-- 同じ全指定境界に属する比較 n 単体の選択空間の可縮性。 -/
lemma loopComparisonBoundaryFiber_isContractibleKan (X Y : OmegaSpectrum.{u}) (n : ℕ)
    (b : ((loopComparisonBoundaryCornerSquare X Y n).pt) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (loopComparisonBoundaryCorner X Y n) b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan (loopComparisonBoundaryCorner X Y n) b

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
