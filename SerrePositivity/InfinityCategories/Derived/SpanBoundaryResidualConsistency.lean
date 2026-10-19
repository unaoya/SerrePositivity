module
public import SerrePositivity.InfinityCategories.Derived.SpanBoundaryZeroData
public import SerrePositivity.InfinityCategories.Derived.SpanResidualCoordinates

/-! # 実際の span 境界の残差整合条件

概要：実際の境界の零未知データから、後続右辺の閉性と脚側右辺の微分公式を得る。
方針：既知方程式と未知成分の零を一般の Bianchi の座標公式に渡す。
規約：HA Proposition 1.3.1.10。使われ方：D7 の有限残差系への入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite DifferentialGraded DGNerve
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：左の零未知データの後続成分は零。
方針：後続集合自身も未知集合であることを使う。
規約：全次元。使われ方：残差を右辺の負に置き換える。 -/
lemma spanBoundaryLeftZeroData_suffixHom {n : ℕ}
    (F : join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ dgNerve A D) :
    (spanBoundaryLeftZeroData F).spanSuffixHom = 0 := by
  exact spanBoundaryLeftZeroData_unknownHom F _ (Finset.Subset.refl _) _ _ _ _ _ _ _

/-- 概要：左の後続右辺は閉じている。
方針：既知方程式を後続集合の Bianchi に渡す。
規約：実際の任意の境界に適用可能。使われ方：有限残差系の最初の整合条件。 -/
lemma spanBoundaryLeftZeroData_suffixRhs_closed {n : ℕ}
    (F : join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ dgNerve A D) :
    differential A (spanBoundaryLeftZeroData F).spanSuffixRhs = 0 :=
  (spanBoundaryLeftZeroData F).spanSuffixRhs_closed (spanBoundaryLeftData_equation F _)

/-- 概要：左の脚側右辺の微分は後続右辺と脚の符号付き合成。
方針：既知方程式と後続成分の零を脚側の Bianchi に渡す。
規約：符号は (-1)^(n+1)。使われ方：cofiber Hom 座標に渡す残差の微分。 -/
lemma spanBoundaryLeftZeroData_onePrefix_differential {n : ℕ}
    (F : join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ dgNerve A D)
    (a : Fin (n + 4)) (ha : a < spanApex n) :
    differential A ((spanBoundaryLeftZeroData F).spanOnePrefixRhs a ha) =
      ((n : ℤ) + 1).negOnePow • compose A
        (spanBoundaryLeftZeroData F).spanSuffixRhs
        ((spanBoundaryLeftZeroData F).edgeHom a (spanApex n) ha) (by omega) :=
  (spanBoundaryLeftZeroData F).spanOnePrefixRhs_differential_of_suffix_zero
    (spanBoundaryLeftData_equation F _) (spanBoundaryLeftZeroData_suffixHom F) a ha

/-- 概要：右の零未知データの後続成分は零。
方針：後続集合自身も未知集合であることを使う。
規約：全次元。使われ方：残差を右辺の負に置き換える。 -/
lemma spanBoundaryRightZeroData_suffixHom {n : ℕ}
    (F : join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ dgNerve A D) :
    (spanBoundaryRightZeroData F).spanSuffixHom = 0 := by
  exact spanBoundaryRightZeroData_unknownHom F _ (Finset.Subset.refl _) _ _ _ _ _ _ _

/-- 概要：右の後続右辺は閉じている。
方針：既知方程式を後続集合の Bianchi に渡す。
規約：実際の任意の境界に適用可能。使われ方：有限残差系の最初の整合条件。 -/
lemma spanBoundaryRightZeroData_suffixRhs_closed {n : ℕ}
    (F : join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ dgNerve A D) :
    differential A (spanBoundaryRightZeroData F).spanSuffixRhs = 0 :=
  (spanBoundaryRightZeroData F).spanSuffixRhs_closed (spanBoundaryRightData_equation F _)

/-- 概要：右の脚側右辺の微分は後続右辺と脚の符号付き合成。
方針：既知方程式と後続成分の零を脚側の Bianchi に渡す。
規約：符号は (-1)^(n+1)。使われ方：cofiber Hom 座標に渡す残差の微分。 -/
lemma spanBoundaryRightZeroData_onePrefix_differential {n : ℕ}
    (F : join (SSet.horn 2 0 : SSet.{max u v}) (SSet.boundary (n + 1)) ⟶ dgNerve A D)
    (a : Fin (n + 4)) (ha : a < spanApex n) :
    differential A ((spanBoundaryRightZeroData F).spanOnePrefixRhs a ha) =
      ((n : ℤ) + 1).negOnePow • compose A
        (spanBoundaryRightZeroData F).spanSuffixRhs
        ((spanBoundaryRightZeroData F).edgeHom a (spanApex n) ha) (by omega) :=
  (spanBoundaryRightZeroData F).spanOnePrefixRhs_differential_of_suffix_zero
    (spanBoundaryRightData_equation F _) (spanBoundaryRightZeroData_suffixHom F) a ha

end SerrePositivity.InfinityCategories
