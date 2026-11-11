module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FiberBoundaryComponents
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanPrefixObjects
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanTwoTailCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-! # 実際の境界の残差の fiber Hom 座標

概要：回収した残差を同じ始点 X と標準 fiber の P,B,C,D の間の cochain に移す。
方針：左右の対象の等式と標準錐の対象の同定に沿う Hom の線形移送を使う。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：未知六成分の線形系を厳密な fiber 座標で解く。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial

/-- 概要：境界の次元に対応する fiber 座標の次数は −n−1。
方針：先頭成分の次数 −n が q+1 となるように取る。
規約：HTT §1.2.13、N7.1。使われ方：六成分の残差を fiber 座標の同じ次数へそろえる。 -/
abbrev fiberBoundaryDegree (n : ℕ) : ℤ := -(n : ℤ) - 1

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：標準 fiber の slice 境界から回収した左の零未知データ。
方針：境界を uncurry して既存の零未知データの構成を使う。
規約：HTT §1.2.13。使われ方：残差の共通の入力データ。 -/
def fiberBoundaryLeftBase {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h))) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (Complex A) (n + 3) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)

/-- 概要：標準 fiber の slice 境界から回収した右の零未知データ。
方針：境界を uncurry して既存の零未知データの構成を使う。
規約：HTT §1.2.13。使われ方：残差の共通の入力データ。 -/
def fiberBoundaryRightBase {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h))) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (Complex A) (n + 3) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)

/-- 概要：fiber の境界残差の共通の始点は左の零番目の対象。
方針：回収した左データの対象を取る。
規約：HTT §1.2.13。使われ方：全ての残差を Hom(X,−) の cochain として読む。 -/
def fiberBoundarySource {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h))) : Complex A :=
  (fiberBoundaryLeftBase g h b).obj 0

/-- 概要：右の零番目の対象は選んだ共通の始点に等しい。
方針：左右の零番目の対象の等式を逆向きに使う。
規約：HTT §1.2.13。使われ方：右の残差の始点を左の始点へ移す。 -/
lemma fiberBoundarySource_right_eq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h))) :
    (fiberBoundaryRightBase g h b).obj 0 = fiberBoundarySource g h b :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryZeroData_zero_obj (A := A) (D := Complex A) (n := n) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)).symm

/-- 概要：先頭の既知の右辺を標準 fiber の Hom 座標に移す。
方針：共通の始点・指定された終点・次数の等式に沿う線形移送を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：未知成分の線形系の r_0。 -/
def fiberBoundaryRhs0 {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    Cochain (fiberBoundarySource g h b) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h) (fiberBoundaryDegree n + 1 + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (D := Complex A) (rfl) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_left_apex g h b hb)
    (by dsimp only [fiberBoundaryDegree]; omega)
    ((fiberBoundaryLeftBase g h b).cospanPrefixRhs)

/-- 概要：B 側の既知の右辺を標準 fiber の Hom 座標に移す。
方針：共通の始点・指定された終点・次数の等式に沿う線形移送を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：未知成分の線形系の r_B。 -/
def fiberBoundaryRhsB {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    Cochain (fiberBoundarySource g h b) (B) (fiberBoundaryDegree n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (D := Complex A) (rfl) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_left_B g h b hb)
    rfl
    ((fiberBoundaryLeftBase g h b).cospanOneTailRhs (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n))

/-- 概要：右側の残差を標準 Hom へ移し、元の射との異種等号も保存する。
方針：対象と次数の移送を証明とともに記録する。
規約：HA Proposition 1.3.1.10。使われ方：具体的な残差の型検査の展開を抑える。 -/
opaque fiberBoundaryRhsCWithHEq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    {z : Cochain (fiberBoundarySource g h b) C (fiberBoundaryDegree n + 1) // HEq z
      ((fiberBoundaryRightBase g h b).cospanOneTailRhs
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n))} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := A) (D := Complex A) (fiberBoundarySource_right_eq g h b)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_right_C g h b hb)
    rfl
    ((fiberBoundaryRightBase g h b).cospanOneTailRhs
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)))

/-- 概要：C 側の既知の右辺を標準 fiber の Hom 座標に移す。
方針：共通の始点・指定された終点・次数の等式に沿う線形移送を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：未知成分の線形系の r_C。 -/
def fiberBoundaryRhsC {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    Cochain (fiberBoundarySource g h b) (C) (fiberBoundaryDegree n + 1) :=
  (fiberBoundaryRhsCWithHEq g h b hb).val

/-- 概要：D 側の左の既知の右辺を標準 fiber の Hom 座標に移す。
方針：共通の始点・指定された終点・次数の等式に沿う線形移送を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：未知成分の線形系の r_D。 -/
def fiberBoundaryRhsD {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    Cochain (fiberBoundarySource g h b) (D) (fiberBoundaryDegree n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (D := Complex A) (rfl) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_left_D g h b hb)
    rfl
    ((fiberBoundaryLeftBase g h b).cospanOneTailRhs (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)))

/-- 概要：左の三角形側の既知の右辺を標準 fiber の Hom 座標に移す。
方針：共通の始点・指定された終点・次数の等式に沿う線形移送を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：未知成分の線形系の r_BD。 -/
def fiberBoundaryRhsBD {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    Cochain (fiberBoundarySource g h b) (D) (fiberBoundaryDegree n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (D := Complex A) (rfl) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_left_D g h b hb)
    (by dsimp only [fiberBoundaryDegree]; omega)
    ((fiberBoundaryLeftBase g h b).cospanTwoTailRhs)

/-- 概要：右側の残差を標準 Hom へ移し、元の射との異種等号も保存する。
方針：対象と次数の移送を証明とともに記録する。
規約：HA Proposition 1.3.1.10。使われ方：具体的な残差の型検査の展開を抑える。 -/
opaque fiberBoundaryRhsCDWithHEq {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    {z : Cochain (fiberBoundarySource g h b) D (fiberBoundaryDegree n) // HEq z
      (fiberBoundaryRightBase g h b).cospanTwoTailRhs} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := A) (D := Complex A) (fiberBoundarySource_right_eq g h b)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberSliceBoundary_right_D g h b hb)
    (by dsimp only [fiberBoundaryDegree]; omega)
    ((fiberBoundaryRightBase g h b).cospanTwoTailRhs))

/-- 概要：右の三角形側の既知の右辺を標準 fiber の Hom 座標に移す。
方針：共通の始点・指定された終点・次数の等式に沿う線形移送を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：未知成分の線形系の r_CD。 -/
def fiberBoundaryRhsCD {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone g h)) :
    Cochain (fiberBoundarySource g h b) (D) (fiberBoundaryDegree n) :=
  (fiberBoundaryRhsCDWithHEq g h b hb).val

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
