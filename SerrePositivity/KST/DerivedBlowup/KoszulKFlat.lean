module

public import SerrePositivity.KST.DerivedBlowup.KoszulConeComparison
public import SerrePositivity.DifferentialGraded.Tensor.Enriched

/-!
概要：KST Def3.1 の有限 Koszul 複体は K-flat である。
方針：単位複体の K-flat 性と cone での閉性を有限列に関して帰納する。
規約：任意の非有界 acyclic 複体を試験対象とする既存 complexKFlat を使う。
使われ方：チャートの項ごとのスカラー拡大を導来スカラー拡大へ比較する。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R : Type u} [CommRing R]

/-- 概要：任意有限列の反復 cone Koszul 複体は K-flat。
方針：空列での単位複体と cone の K-flat 閉性による帰納法。
規約：KST Def3.1、正則性不要。使われ方：導来底変更の計算。 -/
theorem koszulComplex_kFlat : {n : ℕ} → (x : Fin n → R) →
    DifferentialGraded.complexKFlat R (koszulComplex x)
  | 0, _ => DifferentialGraded.complexKFlat_unit R
  | n + 1, x => DifferentialGraded.complexKFlat_cone R
      (smulId (x (Fin.last n)) (koszulComplex (Fin.init x)))
      (koszulComplex_kFlat (Fin.init x)) (koszulComplex_kFlat (Fin.init x))

/-- 概要：任意有限列の外積 Koszul 複体も K-flat。
方針：反復 cone 模型との複体同型で K-flat 性を移す。
規約：KST Def3.1。使われ方：Koszul dg チャートの underlying 複体の K-flat 性。 -/
theorem sequenceExteriorCochain_kFlat {n : ℕ} (x : Fin n → R) :
    DifferentialGraded.complexKFlat R (sequenceExteriorCochain x) :=
  DifferentialGraded.complexKFlat_of_iso R (koszulExteriorIso x).symm (koszulComplex_kFlat x)

/-- 概要：導来 blowup の標準チャートの Koszul 複体は係数多項式環上で K-flat。
方針：チャート関係式の有限列に一般の K-flat 性を適用する。
規約：KST Def3.1。使われ方：重なりへの導来スカラー拡大。 -/
theorem derivedChartComplex_kFlat {r : ℕ} (a : Fin (r + 1) → R) (i : Fin (r + 1)) :
    DifferentialGraded.complexKFlat (ChartRing R i) (derivedChartComplex a i) :=
  koszulComplex_kFlat (chartKoszulSequence a i)

end SerrePositivity.KST.DerivedBlowup
