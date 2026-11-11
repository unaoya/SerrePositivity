module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorCoefficientEquivalence
public import SerrePositivity.EInfinity.BarrattEccles.Theory.NonpositiveHomotopyExtension

/-!
# 二色の指定比較の整数次数と余不変

## 概要
HA 3.2.4.7 の実際の係数比較を、整数コチェイン複体とテンソルの余不変へ移す。

## 方針
非正次数の同型で鎖ホモトピー同値を戻し、加法的な関手によるホモトピーの保存を使う。

## 規約
順射は実際の Hopf 対角と零入力代入で構成した射のまま保つ。

## 使われ方
色付き入力語を持つ自由代数の余積とテンソルの指定比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 実際の二色の始域の係数を、表現の整数コチェイン複体として読む。 -/
def twoColorSourceCochain (m n : ℕ) : CochainComplex (Rep.{u} A (TwoColorGroup.{u} m n)) ℤ :=
  representationCochainComplex (twoColorSourceComplexAction A m n)

/-- 実際の二色のテンソル係数を、表現の整数コチェイン複体として読む。 -/
def twoColorTargetCochain (m n : ℕ) : CochainComplex (Rep.{u} A (TwoColorGroup.{u} m n)) ℤ :=
  representationCochainComplex
    (tensorComplexAction (twoColorLeftAction A m n) (twoColorRightAction A m n))

/-- 整数コチェイン次数での、実際の指定された係数射。 -/
def twoColorCoefficientCochainMap (m n : ℕ) :
    twoColorSourceCochain A m n ⟶ twoColorTargetCochain A m n :=
  representationCochainMap (twoColorSourceComplexAction A m n)
    (tensorComplexAction (twoColorLeftAction A m n) (twoColorRightAction A m n))
    (twoColorCoefficientComparison A m n) (twoColorCoefficientComparison_action A m n)

/-- 始域の係数の表現の複体は非正次数に集中する。 -/
lemma twoColorSourceCochain_isZero_positive (m n : ℕ) (i : ℤ) (hi : 0 < i) :
    IsZero ((twoColorSourceCochain A m n).X i) :=
  representationDegree_isZero A _ i (complex_isZero_positive A (m + n) i hi)

/-- 終域のテンソル係数の表現の複体も非正次数に集中する。 -/
lemma twoColorTargetCochain_isZero_positive (m n : ℕ) (i : ℤ) (hi : 0 < i) :
    IsZero ((twoColorTargetCochain A m n).X i) := by
  apply representationDegree_isZero A
  apply cochainTensor_isZero_X_of_summands
  intro a b hab
  by_cases ha : 0 < a
  · exact Or.inl (complex_isZero_positive A m a ha)
  · exact Or.inr (complex_isZero_positive A n b (by omega))

/-- 整数次数でも、実際の指定係数射は等変な鎖ホモトピー同値の順射である。 -/
def twoColorCoefficientCochainHomotopyEquiv (m n : ℕ) :
    HomotopyEquiv (twoColorSourceCochain A m n) (twoColorTargetCochain A m n) :=
  nonpositiveLiftSpecifiedHomotopyEquiv
    (twoColorSourceCochain_isZero_positive A m n)
    (twoColorTargetCochain_isZero_positive A m n)
    (twoColorCoefficientHomotopyEquiv A m n) (twoColorCoefficientCochainMap A m n) rfl

/-- 整数次数へ戻した同値の順射も元の指定係数射である。 -/
@[simp]
lemma twoColorCoefficientCochainHomotopyEquiv_hom (m n : ℕ) :
    (twoColorCoefficientCochainHomotopyEquiv A m n).hom =
      twoColorCoefficientCochainMap A m n := rfl

/-- 任意の表現をテンソルして余不変を取っても、指定係数比較の同値が保たれる。 -/
def twoColorCoefficientCoinvariantsHomotopyEquiv (m n : ℕ)
    (V : Rep.{u} A (TwoColorGroup.{u} m n)) :
    HomotopyEquiv
      (((Rep.coinvariantsTensor A (TwoColorGroup.{u} m n)).obj V).mapHomologicalComplex
        (.up ℤ) |>.obj (twoColorSourceCochain A m n))
      (((Rep.coinvariantsTensor A (TwoColorGroup.{u} m n)).obj V).mapHomologicalComplex
        (.up ℤ) |>.obj (twoColorTargetCochain A m n)) :=
  ((Rep.coinvariantsTensor A (TwoColorGroup.{u} m n)).obj V).mapHomotopyEquiv
    (twoColorCoefficientCochainHomotopyEquiv A m n)

/-- 余不変を取った同値の順射は、元の係数射へ同じ関手を適用した射である。 -/
@[simp]
lemma twoColorCoefficientCoinvariantsHomotopyEquiv_hom (m n : ℕ)
    (V : Rep.{u} A (TwoColorGroup.{u} m n)) :
    (twoColorCoefficientCoinvariantsHomotopyEquiv A m n V).hom =
      (((Rep.coinvariantsTensor A (TwoColorGroup.{u} m n)).obj V).mapHomologicalComplex
        (.up ℤ)).map (twoColorCoefficientCochainMap A m n) := rfl

end SerrePositivity.EInfinity.BarrattEccles
