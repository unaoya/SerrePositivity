module
public import SerrePositivity.KST.Fibration.Relative.ConnectiveFibrationTheorem
public import SerrePositivity.KST.Fibration.Relative.SuppliedRealization

/-!
概要：Sp の実 c5 を一回代入した K-6 連結 fibration 主定理と K-7 入力。
方針：元の native Verdier 列に対する全次数供給を k6FibrationOfC5 へ渡す。
規約：右辺は供給済み BF 実現。旧固定右辺への輸送は K-6 の範囲外。
使われ方：K-B3 が d・e の同じ実比較と実構造射を追加入力なしで消費する。
-/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.NonConnective
namespace SerrePositivity.KST.Fibration.Relative
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：K-6 の連結 fibration 結論と K-7 向け出力の無条件主定理。
方針：Sp 正本の元の全次数 c5 を条件付き主定理へ一回代入する。
規約：同じ R・D・I のみを固定し、hc5・hIso・hBF・hcofinal は取らない。
使われ方：d・e はこの結論の各射影で消費できる。 -/
theorem k6Fibration : K6FibrationConclusions R D I :=
  k6FibrationOfC5 R D I
    (VerdierSequence.relativeFirstRowSimplexQuotient_localized_isIso
      (dgKappaNativeVerdierDiagram R D I).toVerdierSequence)

/-- 概要：固定 K(D) から同じ実供給 BF 右辺の Sp fiber への非負次数 π 同型。
方針：無条件主定理から元の実比較射の結論を取り出す。
規約：比較先・指定商射は k6Fibration_fiberTarget・k6Fibration_quotientEdge で保持する。
使われ方：K-B3 が消費する d の無条件公開名。 -/
theorem k6Fibration_nonnegative (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (SpectrumHo.piMap (Truncated.HomotopyCategory.homMk
      (dgKappaCanonicalFixedSourceFiberComparison R D I).toTruncated) j) :=
  (k6Fibration R D I).fiber_nonnegative j hj

/-- 概要：元の固定 K の同じ隣接構造射は非負次数 π 同型。
方針：実 c5 と実共終性を代入済みの主定理から e の出力を取り出す。
規約：同じ I・Z を保ち、既存反復射との厳密等号は _eq をそのまま使う。
使われ方：K-7 e の無条件な段別入力。 -/
theorem k6SuspensionStructureMap_nonnegative (Z : DGKappaZeroInput R D I)
    (j : ℤ) (hj : 0 ≤ j) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgKappaCanonicalSuspensionStructureMap R D I Z) j) :=
  (k6Fibration R D I).suspension_nonnegative Z j hj

end SerrePositivity.KST.Fibration.Relative
