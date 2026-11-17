module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteTensorInverse
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TensorNatComponents

/-!
# 有限頭部の標準テンソル–Tot 鎖写像の可逆性

## 概要
元の指定次数成分の逆を、随伴から構成した同じ比較鎖写像の可逆性へ渡す。

## 方針
次数成分の一致と各次数の同型から鎖写像の同型を判定する。

## 規約
横次数で有限な図式に対する法則であり、一般の無限尾部の結論はまだ用いない。

## 使われ方
BS 著者版 Lemma 4.22 の有限頭部の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
variable {R : Type u} [CommRing R]

/-- 横次数が有限な図式について、同じ標準比較鎖写像が同型である。 -/
theorem tensorTotalComparison_isIso_of_finiteRows (L : Complex R)
    (K : CochainComplex (Complex R) ℕ) (N : ℕ)
    (hK : ∀ n : ℕ, N ≤ n → CategoryTheory.Limits.IsZero (K.X n)) :
    IsIso (tensorTotalComparison L K) := by
  haveI (q : ℤ) : IsIso ((tensorTotalComparison L K).f q) := by
    rw [tensorTotalComparison_f_eq]
    exact (finiteTensorComparisonDegreeIso L K N hK q).isIso_hom
  exact HomologicalComplex.Hom.isIso_of_components _

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
