module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.NonConnective.DGSuspensionThomasonComparison
public import SerrePositivity.KST.NonConnective.SequentialCandidatePi

/-!
概要：D-8 の実段供給と実構造辺の逐次 Sp 余極限で、対象別の非連結 K を定義する。
方針：同じ固定 κ・固定 K・実 BF 列を保持し、元の実余錐と整数 π 余極限を公開する。
規約：c4・K-6 d・Sp 安定性を仮定しない。入力全体の関手・局所化登録は別工程。
使われ方：K-7 c5 の対象値 K^{nc}(A)=colim_n Ω^n K(Σ^n Perf A)。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance ncKSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ) (A : PerfDGInput.{u, max (u + 1) v} R)

/-- 同じ実 κ-compact cone の反復による各段の連結固定 K。 -/
def dgNonconnectiveKSuspensionK (n : ℕ) : OmegaSpectrum.{max (u + 1) v} :=
  dgKInputSpectrum R (dgSuspensionUnconditionalIteration R κ hκ A n)

/-- 零段は元の同じ固定 K。 -/
theorem dgNonconnectiveKSuspensionK_zero :
    dgNonconnectiveKSuspensionK R κ hκ A 0 = dgKInputSpectrum R A := rfl

/-- 次段は D-8 の同じ実 cone 入力からの実平坦懸垂 K。 -/
theorem dgNonconnectiveKSuspensionK_succ (n : ℕ) :
    dgNonconnectiveKSuspensionK R κ hκ A (n + 1) =
      dgKInputSpectrum R (dgKappaSuspensionKInput R
        (dgSuspensionUnconditionalIteration R κ hκ A n)
        (dgKappaSelectedConeInput R (dgSuspensionUnconditionalIteration R κ hκ A n)
          κ hκ)) := rfl

/-- 元の実構造辺 K(Σ^n A)→ΩK(Σ^{n+1} A)。全入力自然性は別工程。 -/
def dgNonconnectiveKStructureEdge (n : ℕ) :
    Sp.{max (u + 1) v}.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgNonconnectiveKSuspensionK R κ hκ A n))
      (OmegaSpectrum.nativeLoop.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgNonconnectiveKSuspensionK R κ hκ A (n + 1)))) :=
  dgSuspensionThomasonStructureEdge R κ hκ A n

/-- 同じ実構造辺を n 回 native loop した厳密逐次 BF 図式。 -/
def dgNonconnectiveKDiagram : SpectrumSequence.{max (u + 1) v} :=
  dgSuspensionThomasonSequence R κ hκ A

/-- 同じ逐次図式の n 段。元の Ω^n K(Σ^n A) そのもの。 -/
def dgNonconnectiveKStage (n : ℕ) := (dgNonconnectiveKDiagram R κ hκ A).obj ⟨n⟩

/-- 同じ実隣接射は、元の構造辺を反復 loop して回収した BF 射そのもの。 -/
theorem dgNonconnectiveKDiagram_map_succ (n : ℕ) :
    (dgNonconnectiveKDiagram R κ hκ A).map
        (homOfLE (X := SequentialIndex.{max (u + 1) v}) (Nat.le_succ n)) =
      dgSuspensionNativeSequenceMap R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A
        (dgNonconnectiveKStructureEdge R κ hκ A) n :=
  dgSuspensionNativeSequence_map_succ R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A
    (dgNonconnectiveKStructureEdge R κ hκ A) n

/-- 非連結 K の対象値。固定 κ に対する元の実 Sp 逐次余極限を使う。 -/
def dgNonconnectiveK : OmegaSpectrum.{max (u + 1) v} :=
  sequentialSpectrum (dgNonconnectiveKDiagram R κ hκ A)

/-- 元の実 BF 候補を厳密に保持する。 -/
theorem dgNonconnectiveK_eq_thomasonCandidate :
    dgNonconnectiveK R κ hκ A = dgSuspensionThomasonCandidate R κ hκ A := rfl

/-- 同じ非連結 K を頂点とする実 Sp 余錐。 -/
def dgNonconnectiveKCocone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (dgNonconnectiveKDiagram R κ hκ A)) :=
  sequentialCandidateColimitCocone (dgNonconnectiveKDiagram R κ hκ A)

/-- 余錐の頂点は同じ非連結 K の標準頂点。 -/
theorem dgNonconnectiveKCocone_vertex :
    (dgNonconnectiveKCocone R κ hκ A).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgNonconnectiveK R κ hκ A) :=
  sequentialCandidateColimitCocone_vertex _

/-- 同じ実余錐は全写像空間で余極限。連結版 fibration 入力は不要。 -/
theorem dgNonconnectiveKCocone_isColimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (dgNonconnectiveKCocone R κ hκ A) :=
  sequentialCandidateColimitCocone_isColimit _

/-- 同じ余錐の n 段の実脚を表す BF 射。 -/
def dgNonconnectiveKInjection (n : ℕ) :
    dgNonconnectiveKStage R κ hκ A n ⟶ dgNonconnectiveK R κ hκ A :=
  sequentialCandidateColimitLegHom (dgNonconnectiveKDiagram R κ hκ A) ⟨n⟩

/-- 同じ段の整数 π は元の懸垂 K の j+n 次数を表す。 -/
def dgNonconnectiveKStage_piEquiv (n : ℕ) (j : ℤ) :
    OmegaSpectrum.homotopyGroup (dgNonconnectiveKStage R κ hκ A n) j ≃*
      OmegaSpectrum.homotopyGroup (dgNonconnectiveKSuspensionK R κ hκ A n) (j + n) :=
  dgSuspensionNativeSequenceStage_piEquiv R
    (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n j

/-- 非連結 K の全整数 π は、元の実余錐の脚が与える群余極限。 -/
def dgNonconnectiveKPiCoconeIsColimit (j : ℤ) :
    IsColimit (sequentialCandidatePiCocone (dgNonconnectiveKDiagram R κ hκ A) j) :=
  sequentialCandidatePiCoconeIsColimit _ j

/-- 元の固定 K から非連結 K への零段の実比較射。π 同型性は K-6 d と別照合。 -/
def dgNonconnectiveKConnectiveComparison : dgKInputSpectrum R A ⟶ dgNonconnectiveK R κ hκ A :=
  dgNonconnectiveKInjection R κ hκ A 0

end SerrePositivity.KST.NonConnective

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Def 2.11" (partial := component) "仮定：指定 dg 入力と κ 懸垂の逐次図式（Lean が強い）。結論：非連結 K の対象別候補を構成。任意の導来スキームの Perf(X) からの自然な評価は別（Lean が弱い）。"] _root_.SerrePositivity.KST.NonConnective.dgNonconnectiveK
