module
public import SerrePositivity.InfinityCategories.Derived.SpanTwoPrefixCoordinates
public import SerrePositivity.InfinityCategories.Derived.SpanBoundaryResidualConsistency

/-! # 実際の境界の三角形側残差の微分

概要：左右の実際の零未知境界データについて、三角形側の符号付き微分公式を得る。
方針：境界の既知方程式と全未知成分の零を固定次数の Bianchi に渡す。
規約：可換環上の任意の dg 圏と全次元。使われ方：D7 の六成分残差系への入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite DifferentialGraded DGNerve
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：左の三角形側右辺の微分を三つの右辺の符号付き線形結合で表す。
方針：零未知データの Bianchi に実際の境界の既知方程式と零性を代入する。
規約：追加の整合性を仮定しない。使われ方：左の有限残差系の最後の条件。 -/
lemma spanBoundaryLeftZeroData_twoPrefix_differential {n : ℕ}
    (F : join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ dgNerve A D) :
    differential A (spanBoundaryLeftZeroData F).spanTwoPrefixRhs =
      ((n : ℤ) + 1).negOnePow •
        (compose A (n := -(n : ℤ) - 2 + 1 + 1) (spanBoundaryLeftZeroData F).spanSuffixRhs
          ((spanBoundaryLeftZeroData F).tripleHom 0 (spanSecondPrefix n) (spanApex n)
            (spanSecondPrefix_pos n) (spanSecondPrefix_lt_apex n)) (by omega) +
          (spanBoundaryLeftZeroData F).spanTwoPrefixFirstRhs -
            compose A (n := -(n : ℤ) - 2 + 1 + 1)
              ((spanBoundaryLeftZeroData F).spanOnePrefixRhs
                (spanSecondPrefix n) (spanSecondPrefix_lt_apex n))
              ((spanBoundaryLeftZeroData F).edgeHom
                0 (spanSecondPrefix n) (spanSecondPrefix_pos n)) (by omega)) :=
  (spanBoundaryLeftZeroData F).spanTwoPrefixRhs_differential_of_unknown_zero_normalized
    (spanBoundaryLeftData_equation F _) (spanBoundaryLeftZeroData_unknownHom F)

/-- 概要：右の三角形側右辺の微分を三つの右辺の符号付き線形結合で表す。
方針：零未知データの Bianchi に実際の境界の既知方程式と零性を代入する。
規約：追加の整合性を仮定しない。使われ方：右の有限残差系の最後の条件。 -/
lemma spanBoundaryRightZeroData_twoPrefix_differential {n : ℕ}
    (F : join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ dgNerve A D) :
    differential A (spanBoundaryRightZeroData F).spanTwoPrefixRhs =
      ((n : ℤ) + 1).negOnePow •
        (compose A (n := -(n : ℤ) - 2 + 1 + 1) (spanBoundaryRightZeroData F).spanSuffixRhs
          ((spanBoundaryRightZeroData F).tripleHom 0 (spanSecondPrefix n) (spanApex n)
            (spanSecondPrefix_pos n) (spanSecondPrefix_lt_apex n)) (by omega) +
          (spanBoundaryRightZeroData F).spanTwoPrefixFirstRhs -
            compose A (n := -(n : ℤ) - 2 + 1 + 1)
              ((spanBoundaryRightZeroData F).spanOnePrefixRhs
                (spanSecondPrefix n) (spanSecondPrefix_lt_apex n))
              ((spanBoundaryRightZeroData F).edgeHom
                0 (spanSecondPrefix n) (spanSecondPrefix_pos n)) (by omega)) :=
  (spanBoundaryRightZeroData F).spanTwoPrefixRhs_differential_of_unknown_zero_normalized
    (spanBoundaryRightData_equation F _) (spanBoundaryRightZeroData_unknownHom F)

end SerrePositivity.InfinityCategories
