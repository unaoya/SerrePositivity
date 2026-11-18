module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Complex

/-!
模型。文献の定義との比較は後で
# 全射語の整数次数の比較と零成分

概要：Berger–Fresse §1.2 の非負鎖を整数部分合成の成分として扱う比較を用意する。
方針：非正整数の延長同型を取り、正次数の零対象から元の零性を得る。
規約：整数次数 r は鎖次数 (−r).toNat に対応する。
使われ方：整数次数の双線形部分合成と TR との比較。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.CategoryTheory

variable (A : Type u) [CommRing A]

/-- 概要：非正整数次数の χ の成分は対応する全射語加群（BF §1.2.1）。
方針：次数埋め込みの標準同型を使う。
規約：等式の証明や基底の選択には依存しない。
使われ方：整数部分合成の非零分岐で入力と出力を移す。 -/
def complexXIsoNonpos (n : ℕ) (r : ℤ) (hr : r ≤ 0) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X r ≅ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n (-r).toNat :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (by
    change -(((-r).toNat : ℕ) : ℤ) = r
    omega)

/-- 概要：χ の正次数成分の任意の元は零（BF §1.2.1）。
方針：零対象の加群の台が subsingleton であることを使う。
規約：全 arity。
使われ方：整数部分合成で正次数の入力を除く。 -/
lemma complex_eq_zero_of_positive (n : ℕ) (r : ℤ) (hr : 0 < r)
    (x : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X r) : x = 0 := by
  let _ := ModuleCat.isZero_iff_subsingleton.mp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex_isZero_positive A n r hr)
  exact Subsingleton.elim _ _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
