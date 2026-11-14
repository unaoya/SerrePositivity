module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanTwoPrefixCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanBoundaryResidualConsistency

/-! # 実際の境界の三角形側残差の微分

概要：左右の実際の零未知境界データについて、三角形側の符号付き微分公式を得る。
方針：境界の既知方程式と全未知成分の零を固定次数の Bianchi に渡す。
規約：可換環上の任意の dg 圏と全次元。使われ方：D7 の六成分残差系への入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 概要：左の三角形側右辺の微分を三つの右辺の符号付き線形結合で表す。
方針：零未知データの Bianchi に実際の境界の既知方程式と零性を代入する。
規約：追加の整合性を仮定しない。使われ方：左の有限残差系の最後の条件。 -/
lemma spanBoundaryLeftZeroData_twoPrefix_differential {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).spanTwoPrefixRhs =
      ((n : ℤ) + 1).negOnePow •
        (compose A (n := -(n : ℤ) - 2 + 1 + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).spanSuffixRhs
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).tripleHom 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)) (by omega) +
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).spanTwoPrefixFirstRhs -
            _root_.SerrePositivity.DifferentialGraded.compose A (n := -(n : ℤ) - 2 + 1 + 1)
              ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).spanOnePrefixRhs
                (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n))
              ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).edgeHom
                0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n)) (by omega)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).spanTwoPrefixRhs_differential_of_unknown_zero_normalized
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftData_equation F _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData_unknownHom F)

/-- 概要：右の三角形側右辺の微分を三つの右辺の符号付き線形結合で表す。
方針：零未知データの Bianchi に実際の境界の既知方程式と零性を代入する。
規約：追加の整合性を仮定しない。使われ方：右の有限残差系の最後の条件。 -/
lemma spanBoundaryRightZeroData_twoPrefix_differential {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).spanTwoPrefixRhs =
      ((n : ℤ) + 1).negOnePow •
        (compose A (n := -(n : ℤ) - 2 + 1 + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).spanSuffixRhs
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).tripleHom 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)) (by omega) +
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).spanTwoPrefixFirstRhs -
            _root_.SerrePositivity.DifferentialGraded.compose A (n := -(n : ℤ) - 2 + 1 + 1)
              ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).spanOnePrefixRhs
                (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n))
              ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).edgeHom
                0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_pos n)) (by omega)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).spanTwoPrefixRhs_differential_of_unknown_zero_normalized
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightData_equation F _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData_unknownHom F)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
