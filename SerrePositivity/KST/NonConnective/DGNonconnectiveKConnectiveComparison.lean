module
public import SerrePositivity.KST.NonConnective.DGNonconnectiveK
public import SerrePositivity.KST.Fibration.Relative.ConnectiveFibration
public import SerrePositivity.KST.Fibration.Relative.CanonicalComparison

/-!
概要：到着した K-6 d の構造射判定を同じ非連結 K の実逐次列へ代入する。
方針：同じ実構造射との厳密等号を回収し、無条件 K-6 から隣接安定化・連結比較を得る。
規約：c5 の追加入力なし。K-7 c4 の全入力作用や Sp 安定性は結論しない。
使われ方：c5・d3 の同じ実余錐の零段比較と全整数末尾表示。
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
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.NonConnective
local instance ncKConnectiveSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ) (A : PerfDGInput.{u, max (u + 1) v} R)

/-- 元の実構造辺の全一単体は、K-B の canonical 構造射の全一単体そのもの。 -/
theorem dgNonconnectiveKStructureEdge_canonical (n : ℕ) :
    (dgNonconnectiveKStructureEdge R κ hκ A n).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Relative.dgKappaCanonicalSuspensionStructureMap R
        (dgSuspensionUnconditionalIteration R κ hκ A n)
        (dgSuspensionIterationStage R
          (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n).cone
        (dgSuspensionUnconditionalIteration_zeroInput R κ hκ A n))).edge := by
  rw [Relative.dgKappaCanonicalSuspensionStructureMap_eq R _ _ dgKThomasonCofinality]
  exact (dgKappaNativeStructureMap_edge R _ _ _).symm

/-- 同じ実反復の相対比較は、K-B の無条件 c4・c5 から得られる。 -/
def dgNonconnectiveKCanonicalRelativeComparison (n : ℕ) :
    Relative.SingleRelativeComparison
      (dgKappaNativeVerdierDiagram R (dgSuspensionUnconditionalIteration R κ hκ A n)
        (dgSuspensionIterationStage R
          (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n).cone) :=
  Relative.SingleRelativeComparison.ofCanonicalFirstRowSimplices _
    (VerdierSequence.relativeFirstRowSimplexQuotient_localized_isIso
      (dgKappaNativeVerdierDiagram R (dgSuspensionUnconditionalIteration R κ hκ A n)
        (dgSuspensionIterationStage R
          (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n).cone).toVerdierSequence)

/-- 元の同じ実隣接射は移動後非負範囲で π 同型。 -/
theorem dgNonconnectiveKTransition_nonnegative (n : ℕ) (j : ℤ) (hj : 0 ≤ j + n) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      ((dgNonconnectiveKDiagram R κ hκ A).map
        (homOfLE (X := SequentialIndex.{max (u + 1) v}) (Nat.le_succ n))) j) := by
  rw [dgNonconnectiveKDiagram_map_succ]
  apply (dgSuspensionNativeSequenceMap_bijective_iff_structure R
    (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A _ n j).mpr
  rw [SpectrumHo.piMap_edge]
  exact Relative.k6SuspensionStructureMap_nonnegative R
    (dgSuspensionUnconditionalIteration R κ hκ A n)
    (dgSuspensionIterationStage R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A n).cone
    (dgSuspensionUnconditionalIteration_zeroInput R κ hκ A n) (j + n) hj

/-- 同じ元の固定 K から非連結 K への比較は非負次数 π 同型。 -/
theorem dgNonconnectiveKConnectiveComparison_nonnegative (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgNonconnectiveKConnectiveComparison R κ hκ A) j) :=
  dgSuspensionThomasonConnectedComparison_nonnegative R κ hκ A
    (dgNonconnectiveKCanonicalRelativeComparison R κ hκ A) j hj

/-- 十分後の段の元の実余錐の脚は同じ非連結 K の任意整数 π と同型。 -/
theorem dgNonconnectiveKInjection_tail_bijective (j : ℤ) (n : ℕ) (hn : (-j).toNat ≤ n) :
    Function.Bijective (OmegaSpectrum.homotopyMap (dgNonconnectiveKInjection R κ hκ A n) j) := by
  apply sequentialCandidateLeg_bijective_of_adjacent_tail
  intro m hm
  apply dgNonconnectiveKTransition_nonnegative R κ hκ A m j
  have hb := Int.self_le_toNat (-j)
  omega

/-- 同じ実非連結 K の全整数群を、元の十分後の実懸垂 K の群で表示する。 -/
def dgNonconnectiveK_tailPiEquiv (j : ℤ) (n : ℕ) (hn : (-j).toNat ≤ n) :
    OmegaSpectrum.homotopyGroup (dgNonconnectiveKSuspensionK R κ hκ A n) (j + n) ≃*
      OmegaSpectrum.homotopyGroup (dgNonconnectiveK R κ hκ A) j :=
  (dgNonconnectiveKStage_piEquiv R κ hκ A n j).symm.trans
    (MulEquiv.ofBijective (OmegaSpectrum.homotopyMap (dgNonconnectiveKInjection R κ hκ A n) j)
      (dgNonconnectiveKInjection_tail_bijective R κ hκ A j n hn))

end SerrePositivity.KST.NonConnective
