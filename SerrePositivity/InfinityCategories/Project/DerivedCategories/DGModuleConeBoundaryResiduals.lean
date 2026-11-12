module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConeBoundaryComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanSuffixObjects
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SpanBoundaryTwoPrefixConsistency
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra

/-! # 実際の coslice 境界の残差の cofiber Hom 座標

概要：境界から回収した六つの右辺を標準 cofiber・A・B・C から同じ終点への cochain に移す。
方針：最初の余錐の対象と左右の終点の等式に沿う Hom の線形移送を使う。
規約：任意の非有界複体。使われ方：D7 の六未知成分の線形系への入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial

/-- 概要：境界の次元に対応する cofiber 座標の次数は −n−1。
方針：後続成分の次数 −n が q+1 となるよう選ぶ。
規約：q は整数。使われ方：六つの残差の次数の統一。 -/
abbrev dgModuleConeBoundaryDegree (n : ℕ) : ℤ := -(n : ℤ) - 1

variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 概要：標準 cofiber の coslice 境界から回収した左の零未知データ。
方針：境界を uncurry して既存の組み立てを使う。
規約：最初の頂点の指定は不要。使われ方：残差の共通の入力。 -/
def dgModuleConeBoundaryLeftBase {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) (n + 3) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)

/-- 概要：標準 cofiber の coslice 境界から回収した右の零未知データ。
方針：境界を uncurry して既存の組み立てを使う。
規約：最初の頂点の指定は不要。使われ方：残差の共通の入力。 -/
def dgModuleConeBoundaryRightBase {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A D) (n + 3) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryRightZeroData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)

/-- 概要：境界残差の共通の終点は左データの最後の対象。
方針：回収した対象を選ぶ。
規約：全ての残差はこの対象への射。使われ方：Hom の値域の固定。 -/
def dgModuleConeBoundaryTarget {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f))) : RightModule A D :=
  (dgModuleConeBoundaryLeftBase A D f b).obj (Fin.last (n + 3))

/-- 概要：右データの最後の対象も選んだ終点に等しい。
方針：共通面の最後の対象の等式を逆向きに使う。
規約：境界の指定頂点の条件は不要。使われ方：右の残差の値域の移送。 -/
lemma dgModuleConeBoundaryTarget_right_eq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f))) :
    (dgModuleConeBoundaryRightBase A D f b).obj (Fin.last (n + 3)) = dgModuleConeBoundaryTarget
      A D f b :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryZeroData_last_obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)).symm

/-- 概要：0 側の既知右辺を標準 cofiber の cochain 座標に移す。
方針：指定余錐の対象と共通終点および次数の等式で線形移送する。
規約：異種等号も下記に公開する。使われ方：六成分線形系の r_0。 -/
def dgModuleConeBoundaryRhs0 {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f))
      (dgModuleConeBoundaryTarget A D f b) (dgModuleConeBoundaryDegree n + 1 + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (D := RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_apex A D f b hb)
    (rfl) (by dsimp only [dgModuleConeBoundaryDegree]; omega)
    ((dgModuleConeBoundaryLeftBase A D f b).spanSuffixRhs)

/-- 概要：移送した 0 側右辺は元の境界の右辺と異種等号で一致する。
方針：線形移送の異種等号の公式を使う。
規約：端点と次数の移送を含む。使われ方：微分と合成の整合条件の移送。 -/
lemma dgModuleConeBoundaryRhs0_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    HEq (dgModuleConeBoundaryRhs0 A D f b hb)
    ((dgModuleConeBoundaryLeftBase A D f b).spanSuffixRhs) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq (A := A) (D := RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_apex A D f b hb)
    (rfl) (by dsimp only [dgModuleConeBoundaryDegree]; omega) _

/-- 概要：B 側の既知右辺を標準 cofiber の cochain 座標に移す。
方針：指定余錐の対象と共通終点および次数の等式で線形移送する。
規約：異種等号も下記に公開する。使われ方：六成分線形系の r_B。 -/
def dgModuleConeBoundaryRhsB {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N) (dgModuleConeBoundaryTarget A D f b)
      (dgModuleConeBoundaryDegree n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (D := RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_B A D f b hb)
    (rfl) rfl
    ((dgModuleConeBoundaryLeftBase A D f b).spanOnePrefixRhs
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n))

/-- 概要：移送した B 側右辺は元の境界の右辺と異種等号で一致する。
方針：線形移送の異種等号の公式を使う。
規約：端点と次数の移送を含む。使われ方：微分と合成の整合条件の移送。 -/
lemma dgModuleConeBoundaryRhsB_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    HEq (dgModuleConeBoundaryRhsB A D f b hb)
    ((dgModuleConeBoundaryLeftBase A D f b).spanOnePrefixRhs
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq (A := A) (D := RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_B A D f b hb)
    (rfl) rfl _

/-- 概要：C 側の既知右辺を標準 cofiber の cochain 座標に移す。
方針：指定余錐の対象と共通終点および次数の等式で線形移送する。
規約：異種等号も下記に公開する。使われ方：六成分線形系の r_C。 -/
def dgModuleConeBoundaryRhsC {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (_root_.SerrePositivity.DifferentialGraded.zeroModule A D) (dgModuleConeBoundaryTarget A D f b)
      (dgModuleConeBoundaryDegree n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (D := RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_C A D f b hb)
    (dgModuleConeBoundaryTarget_right_eq A D f b) rfl
    ((dgModuleConeBoundaryRightBase A D f b).spanOnePrefixRhs
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n))

/-- 概要：移送した C 側右辺は元の境界の右辺と異種等号で一致する。
方針：線形移送の異種等号の公式を使う。
規約：端点と次数の移送を含む。使われ方：微分と合成の整合条件の移送。 -/
lemma dgModuleConeBoundaryRhsC_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    HEq (dgModuleConeBoundaryRhsC A D f b hb)
    ((dgModuleConeBoundaryRightBase A D f b).spanOnePrefixRhs
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSecondPrefix_lt_apex n)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq (A := A) (D := RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_C A D f b hb)
    (dgModuleConeBoundaryTarget_right_eq A D f b) rfl _

/-- 概要：A 側の既知右辺を標準 cofiber の cochain 座標に移す。
方針：指定余錐の対象と共通終点および次数の等式で線形移送する。
規約：異種等号も下記に公開する。使われ方：六成分線形系の r_A。 -/
def dgModuleConeBoundaryRhsA {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) (dgModuleConeBoundaryTarget A D f b)
      (dgModuleConeBoundaryDegree n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (D := RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_A A D f b hb)
    (rfl) rfl
    ((dgModuleConeBoundaryLeftBase A D f b).spanOnePrefixRhs 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n))

/-- 概要：移送した A 側右辺は元の境界の右辺と異種等号で一致する。
方針：線形移送の異種等号の公式を使う。
規約：端点と次数の移送を含む。使われ方：微分と合成の整合条件の移送。 -/
lemma dgModuleConeBoundaryRhsA_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    HEq (dgModuleConeBoundaryRhsA A D f b hb)
    ((dgModuleConeBoundaryLeftBase A D f b).spanOnePrefixRhs 0 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex_pos n)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq (A := A) (D := RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_A A D f b hb)
    (rfl) rfl _

/-- 概要：AB 側の既知右辺を標準 cofiber の cochain 座標に移す。
方針：指定余錐の対象と共通終点および次数の等式で線形移送する。
規約：異種等号も下記に公開する。使われ方：六成分線形系の r_AB。 -/
def dgModuleConeBoundaryRhsAB {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) (dgModuleConeBoundaryTarget A D f b)
      (dgModuleConeBoundaryDegree n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (D := RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_A A D f b hb)
    (rfl) (by dsimp only [dgModuleConeBoundaryDegree]; omega)
    ((dgModuleConeBoundaryLeftBase A D f b).spanTwoPrefixRhs)

/-- 概要：移送した AB 側右辺は元の境界の右辺と異種等号で一致する。
方針：線形移送の異種等号の公式を使う。
規約：端点と次数の移送を含む。使われ方：微分と合成の整合条件の移送。 -/
lemma dgModuleConeBoundaryRhsAB_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    HEq (dgModuleConeBoundaryRhsAB A D f b hb)
    ((dgModuleConeBoundaryLeftBase A D f b).spanTwoPrefixRhs) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq (A := A) (D := RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_left_A A D f b hb)
    (rfl) (by dsimp only [dgModuleConeBoundaryDegree]; omega) _

/-- 概要：AC 側の既知右辺を標準 cofiber の cochain 座標に移す。
方針：指定余錐の対象と共通終点および次数の等式で線形移送する。
規約：異種等号も下記に公開する。使われ方：六成分線形系の r_AC。 -/
def dgModuleConeBoundaryRhsAC {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) (dgModuleConeBoundaryTarget A D f b)
      (dgModuleConeBoundaryDegree n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (A := A) (D := RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_A A D f b hb)
    (dgModuleConeBoundaryTarget_right_eq A D f b) (by
      dsimp only [dgModuleConeBoundaryDegree]
      omega)
    ((dgModuleConeBoundaryRightBase A D f b).spanTwoPrefixRhs)

/-- 概要：移送した AC 側右辺は元の境界の右辺と異種等号で一致する。
方針：線形移送の異種等号の公式を使う。
規約：端点と次数の移送を含む。使われ方：微分と合成の整合条件の移送。 -/
lemma dgModuleConeBoundaryRhsAC_heq {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    HEq (dgModuleConeBoundaryRhsAC A D f b hb)
    ((dgModuleConeBoundaryRightBase A D f b).spanTwoPrefixRhs) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq (A := A) (D := RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundary_right_A A D f b hb)
    (dgModuleConeBoundaryTarget_right_eq A D f b) (by
      dsimp only [dgModuleConeBoundaryDegree]
      omega) _

/-- 概要：cofiber Hom 座標へ移した後続右辺は閉じている。
方針：元の境界の後続右辺の閉性を Hom の移送で保つ。
規約：有界性は仮定しない。使われ方：六成分系の最初の整合条件 δr₀=0。 -/
lemma dgModuleConeBoundaryRhs0_closed {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f)) :
    _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A (dgModuleConeBoundaryRhs0 A D f b hb) = 0 := by
  unfold dgModuleConeBoundaryRhs0
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_closed (A := A) (D := RightModule A D)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanBoundaryLeftZeroData_suffixRhs_closed (A := A) (D := RightModule A D) (n := n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
