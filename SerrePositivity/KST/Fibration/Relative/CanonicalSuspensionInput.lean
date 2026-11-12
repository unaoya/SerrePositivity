module
public import SerrePositivity.KST.Fibration.Relative.CanonicalFixedSourceFiber
public import SerrePositivity.KST.SConstruction.Cofinality.Thomason

/-!
概要：d の単回比較を、同じ実商の冪等完備化を経る BGT §9 の実構造射へ渡す。
方針：証明済み Thomason 共終性で完備化比較を放電し、完成した c4・b を代入する。
規約：c5 と同じ I・Z のみを入力に残す。全入力自然性や非連結化後の局所化性は主張しない。
使われ方：K-B3 の K-7 e が、同じ元の固定 K の隣接構造射を消費する入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.NonConnective
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration.Relative
local instance canonicalSuspensionSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory

variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ実商から固定 K への完備化比較は正次数で全単射。
方針：元の Yoneda 完備化比較へ Thomason の実供給を渡す。
規約：共終性や零次全射性を入力に取らない。
使われ方：BGT 入力で一回 loop 前に必要な正次数比較。 -/
theorem dgKappaCanonicalCompletion_positive (j : ℤ) (hj : 0 < j) :
    Function.Bijective (OmegaSpectrum.homotopyMap (dgKappaRawSuspensionToFixedK R D I) j) :=
  dgKappaRawSuspensionToFixedK_positive R D I
    (fun _ _ f hf => Cofinality.kSpectrumMap_cofinality f hf) j hj

/-- 概要：同じ実商の完備化比較は零次で単射。
方針：Thomason の零次単射を元の指定実比較へ渡す。
規約：零次全射性は主張しない。
使われ方：K-7 e の冪等完備化入力の正確な境界。 -/
theorem dgKappaCanonicalCompletion_zero_injective :
    Function.Injective (OmegaSpectrum.homotopyMap (dgKappaRawSuspensionToFixedK R D I) 0) :=
  dgKappaRawSuspensionToFixedK_zero_injective R D I
    (fun _ _ f hf => Cofinality.kSpectrumMap_cofinality f hf)

/-- 概要：同じ実完備化比較を一回 loop した射は非負次数 π 同型。
方針：実供給共終性を元の自然な次数移動の比較へ代入する。
規約：c5 や固定 K 四角形の引き戻し性を使わない。
使われ方：元の実 fibration の標的を固定 K の懸垂値へ戻す。 -/
theorem dgKappaCanonicalCompletionLoop_nonnegative (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
      (dgKappaRawSuspensionToFixedLoopEdge R D I).toTruncated) j) :=
  dgKappaRawSuspensionToFixedLoopEdge_nonnegative R D I
    (fun _ _ f hf => Cofinality.kSpectrumMap_cofinality f hf) j hj

/-- 概要：元の固定 K(D) から元の固定懸垂値の loop への同じ実 BF 構造射。
方針：既存の実構造射に証明済み共終性を渡す。
規約：辺・実商・Yoneda 比較を選び直さず、c5 の存在は構成に含めない。
使われ方：K-B3 が BGT の同じ実反復列の隣接射として消費する。 -/
def dgKappaCanonicalSuspensionStructureMap (Z : DGKappaZeroInput R D I) :=
  dgKappaNativeStructureMap R D I
    (dgKappaSuppliedBFOldFibrationEdge R D I
      (fun _ _ f hf => Cofinality.kSpectrumMap_cofinality f hf) Z)

/-- 概要：共終性証明を既存のものに読み替えても、同じ実 BF 構造射を回収する。
方針：同じ構成の定義と証明引数の非依存性を使う。
規約：入力射や反復列の隣接射を選び直さない。
使われ方：K-B3 の既存 hcofinal 付き逐次列へそのまま代入する。 -/
theorem dgKappaCanonicalSuspensionStructureMap_eq
    (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
        (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
          Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))
    (Z : DGKappaZeroInput R D I) :
    dgKappaCanonicalSuspensionStructureMap R D I Z =
      dgKappaNativeStructureMap R D I (dgKappaSuppliedBFOldFibrationEdge R D I hcofinal Z) := rfl

/-- 概要：同じ元の固定 K 構造射は c5 に条件付きで非負次数 π 同型。
方針：無条件 c4・b の単回比較と無条件共終性を既存の実構造射判定へ渡す。
規約：hIso・hBF・hcofinal や全段の Sp 引き戻し性は入力に取らない。
使われ方：K-7 e が d を消費する、同じ I・Z と元の隣接射の公開界面。 -/
theorem dgKappaCanonicalSuspensionStructureMap_nonnegative
    (Z : DGKappaZeroInput R D I)
    (hq : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeFirstRowSimplexQuotient (dgKappaNativeVerdierDiagram R D I).projection n)))
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgKappaCanonicalSuspensionStructureMap R D I Z) j) :=
  dgKappaSuppliedBFFixedStructureMap_nonnegative R D I
    (fun _ _ f hf => Cofinality.kSpectrumMap_cofinality f hf) Z
    (canonicalSingleS_isPullback (dgKappaNativeVerdierDiagram R D I) hq) j hj

end SerrePositivity.KST.Fibration.Relative
