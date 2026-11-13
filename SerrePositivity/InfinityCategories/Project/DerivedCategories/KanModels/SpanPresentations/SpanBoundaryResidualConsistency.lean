module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanBoundaryZeroData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanResidualCoordinates

/-! # 実際の span 境界の残差整合条件

概要：実際の境界の零未知データから、後続右辺の閉性と脚側右辺の微分公式を得る。
方針：既知方程式と未知成分の零を一般の Bianchi の座標公式に渡す。
規約：HA Proposition 1.3.1.10。使われ方：D7 の有限残差系への入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 概要：左の零未知データの後続成分は零。
方針：後続集合自身も未知集合であることを使う。
規約：全次元。使われ方：残差を右辺の負に置き換える。 -/
lemma spanBoundaryLeftZeroData_suffixHom {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).spanSuffixHom = 0 := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData_unknownHom F _ (Finset.Subset.refl _) _ _ _ _ _ _ _

/-- 概要：左の後続右辺は閉じている。
方針：既知方程式を後続集合の Bianchi に渡す。
規約：実際の任意の境界に適用可能。使われ方：有限残差系の最初の整合条件。 -/
lemma spanBoundaryLeftZeroData_suffixRhs_closed {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).spanSuffixRhs = 0 :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).spanSuffixRhs_closed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftData_equation F _)

/-- 概要：左の脚側右辺の微分は後続右辺と脚の符号付き合成。
方針：既知方程式と後続成分の零を脚側の Bianchi に渡す。
規約：符号は (-1)^(n+1)。使われ方：cofiber Hom 座標に渡す残差の微分。 -/
lemma spanBoundaryLeftZeroData_onePrefix_differential {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (a : Fin (n + 4)) (ha : a < _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) :
    differential A ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).spanOnePrefixRhs a ha) =
      ((n : ℤ) + 1).negOnePow • _root_.SerrePositivity.DifferentialGraded.compose A
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).spanSuffixRhs
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).edgeHom a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) ha) (by omega) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData F).spanOnePrefixRhs_differential_of_suffix_zero
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftData_equation F _) (spanBoundaryLeftZeroData_suffixHom F) a ha

/-- 概要：右の零未知データの後続成分は零。
方針：後続集合自身も未知集合であることを使う。
規約：全次元。使われ方：残差を右辺の負に置き換える。 -/
lemma spanBoundaryRightZeroData_suffixHom {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).spanSuffixHom = 0 := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData_unknownHom F _ (Finset.Subset.refl _) _ _ _ _ _ _ _

/-- 概要：右の後続右辺は閉じている。
方針：既知方程式を後続集合の Bianchi に渡す。
規約：実際の任意の境界に適用可能。使われ方：有限残差系の最初の整合条件。 -/
lemma spanBoundaryRightZeroData_suffixRhs_closed {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).spanSuffixRhs = 0 :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).spanSuffixRhs_closed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightData_equation F _)

/-- 概要：右の脚側右辺の微分は後続右辺と脚の符号付き合成。
方針：既知方程式と後続成分の零を脚側の Bianchi に渡す。
規約：符号は (-1)^(n+1)。使われ方：cofiber Hom 座標に渡す残差の微分。 -/
lemma spanBoundaryRightZeroData_onePrefix_differential {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (a : Fin (n + 4)) (ha : a < _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) :
    differential A ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).spanOnePrefixRhs a ha) =
      ((n : ℤ) + 1).negOnePow • _root_.SerrePositivity.DifferentialGraded.compose A
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).spanSuffixRhs
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).edgeHom a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) ha) (by omega) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData F).spanOnePrefixRhs_differential_of_suffix_zero
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightData_equation F _) (spanBoundaryRightZeroData_suffixHom F) a ha

end SerrePositivity.InfinityCategories.Project.DerivedCategories
