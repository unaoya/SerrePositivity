-- 移行先：SerrePositivity.BhattScholze.Perfectoidization.Derived.RootAdjunction。
module

public import SerrePositivity.BhattScholze.Perfectoidization.Derived.RootAdjunction
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic

/-!
# 根添加の残る定理

## 概要
濃度、代数的根添加の filtered 余極限との可換性、有限変数の根添加環の
完全忠実平坦性を扱う。

## 方針
移行済みの根添加の構成・延長性・関手性と perfectoid 性を利用する。
設計は a5-design.md §3.1〜§3.3。

## 規約
本ファイルは drafts として保持する。

## 使われ方
A5-4 の弱始対象と降下、A6-1 の perfectoid 被覆。
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.PerfectoidizationInterface

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
variable (S : Type u) [CommRing S] [Algebra R S]

/-- 概要：(iii) #S̃ ≤ (#S + ℵ₀)^{ℵ₀}（各段は #S_k + ℵ₀ 個の変数の多項式環の商、可算余極限、完備化は可算列の逆極限）。
方針：各段の濃度評価と完備化の濃度（A0 `cardinal_envelope_le` と同型の議論）。
規約：κ = `cutoff` 以上の κ（`IsAdmissibleCutoff`、κ^{ℵ₀} = κ）なら ≤ κ。
使われ方：κ 側の site の対象になること（D47）。 -/
theorem rootClosure_cardinal_le : Cardinal.mk (rootClosure p R S) ≤ (Cardinal.mk S + Cardinal.aleph0) ^ Cardinal.aleph0 := by
  sorry -- 可算個の段と可算完備化の濃度評価

/-- 概要：E(−) は通常の環の filtered 余極限と可換（各元と各等式が有限個の変数と関係だけを使うので）。
方針：`MvPolynomial` の余極限との交換。filtered 図式の標準射 `colimit.post` の可逆性で述べる。
規約：—
使われ方：A5-4 `algebraicRootCover_properties`。 -/
theorem algebraicRootClosure_filteredColimit {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{u}) : IsIso (Limits.colimit.post D (algebraicRootFunctor p)) := by
  sorry -- 一つの多項式と関係の有限和は有限段から来る。各段の比較と ω 余極限を交換する

include hR in
/-- 概要：T → T_∞ は p 完備忠実平坦（T_∞ は T 上、単項式 X^{a}（a ∈ (ℤ[1/p] ∩ [0,1))^r）を基底とする自由加群の p 完備化）。よって S → S̃ も。
方針：基底の明示。
規約：記録（降下の前提は Lemma 8.6 の descendability で、忠実平坦性は直接は使わない）。
使われ方：原典 (3) との対応。 -/
theorem polyAlgebraToRoot_pCompletelyFaithfullyFlat (r : ℕ) :
    letI := (polyAlgebraToRoot p R r).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : polyAlgebra p R r)}) (polyRootAlgebra p R r) := by
  sorry -- p 冪分母で各座標が [0,1) の指数をもつ単項式が完備自由基底。mod p は 1 を含む自由基底をもつ

end SerrePositivity.BhattScholze.Perfectoidization.Derived
