module

public import SerrePositivity.KST.NonConnective.DGSuspensionPerfectConnectiveSequence
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionConnectivePi

/-!
概要：同じ実評価 Perf 比較を使う反復列の構造射に、連結版 fibration の次数条件を適用する。
方針：各段の元の実 fiber 比較を用い、j+n が非負となる具体的範囲を保持する。
規約：段別 I・P・Z と連結版 K-6 の非負次数比較に条件付き。Sp 引き戻し性は使わない。
使われ方：K-7 d3。構造射と native loop 反復遷移の π 自然性は Sp 正本との接続を残す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ) (A : PerfDGInput.{u, max (u + 1) v} R)
  (Z : ∀ n, DGKappaZeroInput R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone)

variable (h : ∀ (n : ℕ) (k : ℤ), 0 ≤ k → Function.Bijective
  (dgConnectiveFiberComparisonPi R
    (dgKappaResolvedConnectiveSquare R (dgSuspensionIteration R s A n)
      (dgSuspensionIterationStage R s A n).cone)
    (dgKappaResolvedConnectiveSquare_zero_corner R (dgSuspensionIteration R s A n)
      (dgSuspensionIterationStage R s A n).cone (dgKappaResolvedNullPerf_isZero R
        (dgSuspensionIteration R s A n) (dgSuspensionIterationStage R s A n).cone)) k).hom)

include h in
/-- 概要：段別連結版 fiber 比較に条件付きで、元の実構造射は j+n 非負の範囲で π 同型。
方針：同じ実評価 Perf 比較と実零角を、同じ段の構造射の判定へ代入する。
規約：別の Perf 同値や全整数の fiber 同型を仮定しない。
使われ方：非負次数の隣接安定化への元の構造射側の入力。 -/
theorem dgSuspensionPerfectStructureMap_shifted_bijective (n : ℕ) (j : ℤ)
    (hj : 0 ≤ j + n) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgKappaResolvedConnectiveStructureMap R (dgSuspensionIteration R s A n)
        (dgSuspensionIterationStage R s A n).cone (dgSuspensionResolvedPerfEquivalence R s A n)
        (Z n) (dgKappaResolvedNullPerf_isZero R (dgSuspensionIteration R s A n)
          (dgSuspensionIterationStage R s A n).cone)) (j + n)) :=
  dgKappaResolvedConnectiveStructureMap_nonnegative R (dgSuspensionIteration R s A n)
    (dgSuspensionIterationStage R s A n).cone (dgSuspensionResolvedPerfEquivalence R s A n)
    (Z n) (h n) (j + n) hj

include h in
/-- 概要：段別連結版 fiber 比較に条件付きで、全非負次数 j の構造射は全反復段で π 同型。
方針：j+n の非負性を元の j と自然数 n から検証する。
規約：native loop 反復後の遷移の自然性はこの算術から推論しない。
使われ方：同じ実余錐の連結比較へ渡す次数範囲。 -/
theorem dgSuspensionPerfectStructureMap_nonnegative (j : ℤ) (hj : 0 ≤ j) (n : ℕ) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgKappaResolvedConnectiveStructureMap R (dgSuspensionIteration R s A n)
        (dgSuspensionIterationStage R s A n).cone (dgSuspensionResolvedPerfEquivalence R s A n)
        (Z n) (dgKappaResolvedNullPerf_isZero R (dgSuspensionIteration R s A n)
          (dgSuspensionIterationStage R s A n).cone)) (j + n)) :=
  dgSuspensionPerfectStructureMap_shifted_bijective R s A Z h n j (by omega)

include h in
/-- 概要：段別連結版 fiber 比較に条件付きで、任意整数 j での構造射の有効な末尾範囲。
方針：n が (-j).toNat 以上なら j+n は非負と検証する。
規約：対象候補の負群消滅や BF 遷移の安定化をまだ主張しない。
使われ方：非連結化後の全整数 π を調べる際の段数の境界。 -/
theorem dgSuspensionPerfectStructureMap_tail (j : ℤ) (n : ℕ) (hn : (-j).toNat ≤ n) :
    Function.Bijective (OmegaSpectrum.homotopyMap
      (dgKappaResolvedConnectiveStructureMap R (dgSuspensionIteration R s A n)
        (dgSuspensionIterationStage R s A n).cone (dgSuspensionResolvedPerfEquivalence R s A n)
        (Z n) (dgKappaResolvedNullPerf_isZero R (dgSuspensionIteration R s A n)
          (dgSuspensionIterationStage R s A n).cone)) (j + n)) :=
  dgSuspensionPerfectStructureMap_shifted_bijective R s A Z h n j (by omega)

end SerrePositivity.KST.NonConnective
