module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFiberBoundaryComponents
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanPrefixObjects
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CospanTwoTailCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-! # 実際の境界の残差の fiber Hom 座標

概要：回収した残差を同じ始点 X とdg 加群の標準 fiber の P,B,C,D の間の 全 Hom end の成分 に移す。
方針：左右の対象の等式と標準錐の対象の同定に沿う Hom の線形移送を使う。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：未知六成分の線形系を厳密な fiber 座標で解く。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

/-- 概要：境界の次元に対応する fiber 座標の次数は −n−1。
方針：先頭成分の次数 −n が q+1 となるように取る。
規約：HTT §1.2.13、N7.1。使われ方：六成分の残差を fiber 座標の同じ次数へそろえる。 -/
abbrev dgModuleFiberBoundaryDegree (n : ℕ) : ℤ := -(n : ℤ) - 1

variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 概要：dg 加群の標準 fiber の slice 境界から回収した左の零未知データ。
方針：境界を uncurry して既存の零未知データの構成を使う。
規約：HTT §1.2.13。使われ方：残差の共通の入力データ。 -/
def dgModuleFiberBoundaryLeftBase {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f))) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) (n
        + 3) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)

/-- 概要：dg 加群の標準 fiber の slice 境界から回収した右の零未知データ。
方針：境界を uncurry して既存の零未知データの構成を使う。
規約：HTT §1.2.13。使われ方：残差の共通の入力データ。 -/
def dgModuleFiberBoundaryRightBase {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f))) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) (n
        + 3) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry b)

/-- 概要：fiber の境界残差の共通の始点は左の零番目の対象。
方針：回収した左データの対象を取る。
規約：HTT §1.2.13。使われ方：全ての残差を 全 Hom end の Hom(X,−) の成分として読む。 -/
def dgModuleFiberBoundarySource {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f))) : RightModule A D :=
  (dgModuleFiberBoundaryLeftBase A D f b).obj 0

/-- 概要：右の零番目の対象は選んだ共通の始点に等しい。
方針：左右の零番目の対象の等式を逆向きに使う。
規約：HTT §1.2.13。使われ方：右の残差の始点を左の始点へ移す。 -/
lemma dgModuleFiberBoundarySource_right_eq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f))) :
    (dgModuleFiberBoundaryRightBase A D f b).obj 0 = dgModuleFiberBoundarySource A D f b :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanBoundaryZeroData_zero_obj (A := A) (D := RightModule A D) (n := n) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry
    b)).symm

/-- 概要：先頭の既知の右辺を dg 加群の標準 fiber の Hom 座標に移す。
方針：共通の始点・指定された終点・次数の等式に沿う線形移送を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：未知成分の線形系の r_0。 -/
def dgModuleFiberBoundaryRhs0 {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    GradedHom A (dgModuleFiberBoundarySource A D f b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f)
      (dgModuleFiberBoundaryDegree n + 1 + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (D := RightModule A D) (rfl) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_left_apex A D f
    b hb)
    (by dsimp only [dgModuleFiberBoundaryDegree]; omega)
    ((dgModuleFiberBoundaryLeftBase A D f b).cospanPrefixRhs)

/-- 概要：B 側の既知の右辺を dg 加群の標準 fiber の Hom 座標に移す。
方針：共通の始点・指定された終点・次数の等式に沿う線形移送を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：未知成分の線形系の r_B。 -/
def dgModuleFiberBoundaryRhsM {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (dgModuleFiberBoundarySource A D f b) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
      (dgModuleFiberBoundaryDegree n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (D := RightModule A D) (rfl) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_left_M A D f b hb)
    rfl
    ((dgModuleFiberBoundaryLeftBase A D f b).cospanOneTailRhs (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n))

/-- 概要：右側の残差を標準 Hom へ移し、元の射との異種等号も保存する。
方針：対象と次数の移送を証明とともに記録する。
規約：HA Proposition 1.3.1.10。使われ方：具体的な残差の型検査の展開を抑える。 -/
opaque dgModuleFiberBoundaryRhsZeroWithHEq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    {z : _root_.SerrePositivity.DifferentialGraded.GradedHom A (dgModuleFiberBoundarySource A D f b) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A)
      (_root_.SerrePositivity.DifferentialGraded.moduleZero A D)) (dgModuleFiberBoundaryDegree n + 1) // HEq z
      ((dgModuleFiberBoundaryRightBase A D f b).cospanOneTailRhs
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n))} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := A) (D := RightModule A D) (dgModuleFiberBoundarySource_right_eq
    A D f b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_right_zero A D f b hb)
    rfl
    ((dgModuleFiberBoundaryRightBase A D f b).cospanOneTailRhs
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n)))

/-- 概要：C 側の既知の右辺を dg 加群の標準 fiber の Hom 座標に移す。
方針：共通の始点・指定された終点・次数の等式に沿う線形移送を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：未知成分の線形系の r_C。 -/
def dgModuleFiberBoundaryRhsZero {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (dgModuleFiberBoundarySource A D f b) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleZero
      A D)) (dgModuleFiberBoundaryDegree n + 1) :=
  (dgModuleFiberBoundaryRhsZeroWithHEq A D f b hb).val

/-- 概要：D 側の左の既知の右辺を dg 加群の標準 fiber の Hom 座標に移す。
方針：共通の始点・指定された終点・次数の等式に沿う線形移送を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：未知成分の線形系の r_D。 -/
def dgModuleFiberBoundaryRhsN {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (dgModuleFiberBoundarySource A D f b) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)
      (dgModuleFiberBoundaryDegree n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (D := RightModule A D) (rfl) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_left_N A D f b hb)
    rfl
    ((dgModuleFiberBoundaryLeftBase A D f b).cospanOneTailRhs (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanLastTail n)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanApex_lt_firstTail n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cospanFirstTail_lt_lastTail n)))

/-- 概要：左の三角形側の既知の右辺を dg 加群の標準 fiber の Hom 座標に移す。
方針：共通の始点・指定された終点・次数の等式に沿う線形移送を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：未知成分の線形系の r_BD。 -/
def dgModuleFiberBoundaryRhsMN {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (dgModuleFiberBoundarySource A D f b) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)
      (dgModuleFiberBoundaryDegree n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (D := RightModule A D) (rfl) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_left_N A D f b hb)
    (by dsimp only [dgModuleFiberBoundaryDegree]; omega)
    ((dgModuleFiberBoundaryLeftBase A D f b).cospanTwoTailRhs)

/-- 概要：右側の残差を標準 Hom へ移し、元の射との異種等号も保存する。
方針：対象と次数の移送を証明とともに記録する。
規約：HA Proposition 1.3.1.10。使われ方：具体的な残差の型検査の展開を抑える。 -/
opaque dgModuleFiberBoundaryRhsZeroNWithHEq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    {z : _root_.SerrePositivity.DifferentialGraded.GradedHom A (dgModuleFiberBoundarySource A D f b) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)
      (dgModuleFiberBoundaryDegree n) // HEq z
      (dgModuleFiberBoundaryRightBase A D f b).cospanTwoTailRhs} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := A) (D := RightModule A D) (dgModuleFiberBoundarySource_right_eq
    A D f b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberBoundary_right_N A D f b hb)
    (by dsimp only [dgModuleFiberBoundaryDegree]; omega)
    ((dgModuleFiberBoundaryRightBase A D f b).cospanTwoTailRhs))

/-- 概要：右の三角形側の既知の右辺を dg 加群の標準 fiber の Hom 座標に移す。
方針：共通の始点・指定された終点・次数の等式に沿う線形移送を使う。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：未知成分の線形系の r_CD。 -/
def dgModuleFiberBoundaryRhsZeroN {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D f)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (dgModuleFiberBoundarySource A D f b) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)
      (dgModuleFiberBoundaryDegree n) :=
  (dgModuleFiberBoundaryRhsZeroNWithHEq A D f b hb).val

end SerrePositivity.InfinityCategories.Project.DerivedCategories
