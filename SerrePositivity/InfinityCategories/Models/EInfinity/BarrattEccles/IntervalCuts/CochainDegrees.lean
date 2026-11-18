module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InputLinearIdentities

/-!
模型。文献の定義との比較は後で
# 区間余演算の整数微分と零成分

概要：Berger–Fresse §2.2.7 の線形微分条件を整数複体の次数比較へ移す。
方針：χ の零延長微分を評価し、区間の二つ以外の次数を零対象で処理する。
規約：整数コチェイン次数で全 arity を扱う。
使われ方：全整数 Leibniz 則の次数分岐。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：χ の整数負次数微分の値は全射語の削除微分（BF §1.2.3）。
方針：零延長の微分公式を次数比較同型で評価する。
規約：自然数語次数 d+1 から d。
使われ方：余演算の第一因子の微分項を移す。 -/
lemma surjection_d_neg_apply (n d : ℕ)
    (x : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X (-((d + 1 : ℕ) : ℤ))) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).hom
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).d (-((d + 1 : ℕ) : ℤ)) (-(d : ℤ)) x) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n (d + 1)).hom x) := by
  have h := extend_d_eq (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.normalizedChains A n)
    ComplexShape.embeddingDownNat (i := d + 1) (j := d) rfl rfl
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).d (-((d + 1 : ℕ) : ℤ)) (-(d : ℤ)) =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n (d + 1)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.normalizedChains A n).d (d + 1) d ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).inv at h
  rw [h, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.normalizedChains_d]
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).toLinearEquiv
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).toLinearEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n (d + 1)).hom x))) = _
  exact LinearEquiv.apply_symm_apply _ _

/-- 概要：整数区間の零と −1 以外の次数の元は零（BF §2.1）。
方針：正次数は零延長、負次数は正規化区間の高次零性を使う。
規約：任意の元について述べる。
使われ方：Leibniz 則の区間入力の残余分岐。 -/
lemma interval_eq_zero_of_other (s : ℤ) (h0 : s ≠ 0) (h1 : s ≠ -1)
    (y : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X s) : y = 0 := by
  by_cases hs : 0 < s
  · let _ := ModuleCat.isZero_iff_subsingleton.mp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval_isZero_positive A s hs)
    exact Subsingleton.elim _ _
  · have he : -(((-s).toNat : ℕ) : ℤ) = s := by omega
    let e := extendXIso (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalChains A) ComplexShape.embeddingDownNat he
    let _ := ModuleCat.isZero_iff_subsingleton.mp
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.intervalChains_isZero A (-s).toNat (by omega))
    exact e.toLinearEquiv.injective (Subsingleton.elim _ _)

/-- 概要：χ の正次数の余演算成分は零（BF §2.2.6）。
方針：定義の非正分岐を除く。
規約：出力次数の任意の和の証明。
使われ方：零語次数の微分後の成分を除く。 -/
lemma cochainActionBilinear_eq_zero_of_positive (n : ℕ) (r s t : ℤ) (h : r + s = t)
    (hr : 0 < r) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionBilinear A n r s t h = 0 := by
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionBilinear, show ¬r ≤ 0 by omega]

/-- 概要：区間の零・−1 以外の入力次数の余演算成分は零（BF §2.2.6）。
方針：定義の区間入力の二分岐を除く。
規約：第一入力次数は任意。
使われ方：頂点入力の微分後の成分を除く。 -/
lemma cochainActionBilinear_eq_zero_of_other (n : ℕ) (r s t : ℤ) (h : r + s = t)
    (h0 : s ≠ 0) (h1 : s ≠ -1) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionBilinear A n r s t h = 0 := by
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionBilinear, h0, h1]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
