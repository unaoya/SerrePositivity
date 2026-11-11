module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanOneTailResidual

/-! # 実際の境界からの零未知データの残差整合条件

概要：未知成分を零にした左右の境界データの先頭と脚の右辺の整合条件を証明する。
方針：既知の全方程式と先頭成分の零を確認して、Bianchi の座標公式を適用する。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：N7c の fiber 座標へ渡す既知の右辺。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：左セルの未知成分を全て零とした境界データ。
方針：左の組み立てデータに零の射族を指定する。
規約：HA Proposition 1.3.1.10。使われ方：左の右辺の既知残差の計算。 -/
def cospanBoundaryLeftZeroData {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftData F (fun _ _ _ _ _ _ _ _ => 0)

/-- 概要：右セルの未知成分を全て零とした境界データ。
方針：右の組み立てデータに零の射族を指定する。
規約：HA Proposition 1.3.1.10。使われ方：右の右辺の既知残差の計算。 -/
def cospanBoundaryRightZeroData {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 3) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightData F (fun _ _ _ _ _ _ _ _ => 0)

/-- 概要：左の零未知データの先頭の未知成分は零。
方針：先頭の全てを含む集合では未知の射族の分岐になることを使う。
規約：HA Proposition 1.3.1.10。使われ方：先頭残差を右辺の負に書く。 -/
lemma cospanBoundaryLeftZeroData_prefixHom {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    (cospanBoundaryLeftZeroData F).cospanPrefixHom = 0 := by
  have hn : ¬ ∃ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n, j ∉ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n := by simp
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixHom, cospanBoundaryLeftZeroData, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftData,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly.assembleData, dite_eq_right hn]

/-- 概要：右の零未知データの先頭の未知成分は零。
方針：先頭の全てを含む集合では未知の射族の分岐になることを使う。
規約：HA Proposition 1.3.1.10。使われ方：先頭残差を右辺の負に書く。 -/
lemma cospanBoundaryRightZeroData_prefixHom {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    (cospanBoundaryRightZeroData F).cospanPrefixHom = 0 := by
  have hn : ¬ ∃ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n, j ∉ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixFaces n := by simp
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanPrefixHom, cospanBoundaryRightZeroData, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightData,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly.assembleData, dite_eq_right hn]

/-- 概要：実際の境界からの左の先頭右辺は閉じている。
方針：零未知データの既知方程式に先頭の Bianchi の閉性を適用する。
規約：HA Proposition 1.3.1.10。使われ方：左の δr₀=0。 -/
lemma cospanBoundaryLeftZeroData_prefixRhs_closed {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    differential A (cospanBoundaryLeftZeroData F).cospanPrefixRhs = 0 :=
  (cospanBoundaryLeftZeroData F).cospanPrefixRhs_closed
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftData_equation F _)

/-- 概要：実際の境界からの右の先頭右辺は閉じている。
方針：零未知データの既知方程式に先頭の Bianchi の閉性を適用する。
規約：HA Proposition 1.3.1.10。使われ方：右の δr₀=0。 -/
lemma cospanBoundaryRightZeroData_prefixRhs_closed {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    differential A (cospanBoundaryRightZeroData F).cospanPrefixRhs = 0 :=
  (cospanBoundaryRightZeroData F).cospanPrefixRhs_closed
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightData_equation F _)

/-- 概要：左の脚側右辺の微分は、その脚と先頭右辺の合成の負。
方針：実際の既知方程式と先頭成分の零を脚側 Bianchi へ渡す。
規約：HA Proposition 1.3.1.10。使われ方：左の δr_B=−p r₀ と δr_D=−t r₀。 -/
lemma cospanBoundaryLeftZeroData_oneTail_differential {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (b : Fin (n + 4)) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n < b) :
    differential A ((cospanBoundaryLeftZeroData F).cospanOneTailRhs b hb) =
      -compose A ((cospanBoundaryLeftZeroData F).edgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) b hb)
        (cospanBoundaryLeftZeroData F).cospanPrefixRhs (by omega) :=
  (cospanBoundaryLeftZeroData F).cospanOneTailRhs_differential_of_prefix_zero
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftData_equation F _) (cospanBoundaryLeftZeroData_prefixHom F) b hb

/-- 概要：右の脚側右辺の微分は、その脚と先頭右辺の合成の負。
方針：実際の既知方程式と先頭成分の零を脚側 Bianchi へ渡す。
規約：HA Proposition 1.3.1.10。使われ方：右の δr_C=−q r₀ と δr_D=−t r₀。 -/
lemma cospanBoundaryRightZeroData_oneTail_differential {n : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (SSet.boundary (n + 1) : SSet.{max u v}) (SSet.horn 2 2) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (b : Fin (n + 4)) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n < b) :
    differential A ((cospanBoundaryRightZeroData F).cospanOneTailRhs b hb) =
      -compose A ((cospanBoundaryRightZeroData F).edgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex n) b hb)
        (cospanBoundaryRightZeroData F).cospanPrefixRhs (by omega) :=
  (cospanBoundaryRightZeroData F).cospanOneTailRhs_differential_of_prefix_zero
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightData_equation F _) (cospanBoundaryRightZeroData_prefixHom F) b hb

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
