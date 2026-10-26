module
public import SerrePositivity.KST.Fibration.Relative.SingleStageDetection
public import SerrePositivity.KST.Fibration.Relative.CanonicalRealization

/-!
概要：c4 と b を統合した単回比較から、同じ native 実 fiber の非負次数 π 同型を得る。
方針：元の D-9 列へ canonical 比較を代入し、既存の第一正段検出を消費する。
規約：c5 の標準単体商比較だけを残す。固定 ν の Verdier 認証は使わない。
使われ方：K-6 d の組み立てと K-B3 の K-7 e への公開入力。
-/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.NonConnective
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration.Relative
local instance canonicalSingleStageSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory

variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (hq : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
    (relativeFirstRowSimplexQuotient (dgKappaNativeVerdierDiagram R D I).projection n)))

include hq in
/-- 概要：同じ実供給 BF fiber 比較は c5 に条件付きで非負次数 π 同型。
方針：完成した c4 と相対実現の界面を元の単回検出へ代入する。
規約：hIso・hBF・共終性・全正反復収縮は入力に取らない。
使われ方：未完備実列の d を同じ元の比較辺で証明する。 -/
theorem dgKappaCanonicalFiberComparison_nonnegative (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
      (SSet.Edge.ofTruncated (dgKappaSuppliedBFFiberComparison R D I)).toTruncated) j) :=
  dgKappaRelativeFiberComparison_nonnegative R D I
    (SingleRelativeComparison.ofCanonicalFirstRowSimplices
      (dgKappaNativeVerdierDiagram R D I) hq) j hj

/-- 概要：同じ実比較射の非負次数 π 作用を順方向とする群同型。
方針：実比較射の全単射性から群同型を構成する。
規約：抽象的な両端の群同型へ置き換えず、元の piMap をそのまま使う。
使われ方：K-B3 が同じ native 比較の π 同型を消費する。 -/
def dgKappaCanonicalFiberComparisonPiEquiv (j : ℤ) (hj : 0 ≤ j) :=
  MulEquiv.ofBijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
    (SSet.Edge.ofTruncated (dgKappaSuppliedBFFiberComparison R D I)).toTruncated) j)
      (dgKappaCanonicalFiberComparison_nonnegative R D I hq j hj)

end SerrePositivity.KST.Fibration.Relative
