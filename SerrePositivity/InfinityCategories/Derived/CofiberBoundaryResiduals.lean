module
public import SerrePositivity.InfinityCategories.Derived.CofiberBoundaryComponents
public import SerrePositivity.InfinityCategories.Derived.SpanSuffixObjects
public import SerrePositivity.InfinityCategories.Derived.SpanBoundaryTwoPrefixConsistency
public import SerrePositivity.InfinityCategories.DGNerve.HomHEqAlgebra

/-! # 実際の coslice 境界の残差の cofiber Hom 座標

概要：境界から回収した六つの右辺を標準 cofiber・A・B・C から同じ終点への cochain に移す。
方針：最初の余錐の対象と左右の終点の等式に沿う Hom の線形移送を使う。
規約：任意の非有界複体。使われ方：D7 の六未知成分の線形系への入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial

/-- 概要：境界の次元に対応する cofiber 座標の次数は −n−1。
方針：後続成分の次数 −n が q+1 となるよう選ぶ。
規約：q は整数。使われ方：六つの残差の次数の統一。 -/
abbrev cofiberBoundaryDegree (n : ℕ) : ℤ := -(n : ℤ) - 1

variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- 概要：標準 cofiber の coslice 境界から回収した左の零未知データ。
方針：境界を uncurry して既存の組み立てを使う。
規約：最初の頂点の指定は不要。使われ方：残差の共通の入力。 -/
def cofiberBoundaryLeftBase {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g))) :
    SimplexData S (Complex S) (n + 3) :=
  spanBoundaryLeftZeroData (sliceUnderUncurry b)

/-- 概要：標準 cofiber の coslice 境界から回収した右の零未知データ。
方針：境界を uncurry して既存の組み立てを使う。
規約：最初の頂点の指定は不要。使われ方：残差の共通の入力。 -/
def cofiberBoundaryRightBase {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g))) :
    SimplexData S (Complex S) (n + 3) :=
  spanBoundaryRightZeroData (sliceUnderUncurry b)

/-- 概要：境界残差の共通の終点は左データの最後の対象。
方針：回収した対象を選ぶ。
規約：全ての残差はこの対象への射。使われ方：Hom の値域の固定。 -/
def cofiberBoundaryTarget {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g))) : Complex S :=
  (cofiberBoundaryLeftBase f g b).obj (Fin.last (n + 3))

/-- 概要：右データの最後の対象も選んだ終点に等しい。
方針：共通面の最後の対象の等式を逆向きに使う。
規約：境界の指定頂点の条件は不要。使われ方：右の残差の値域の移送。 -/
lemma cofiberBoundaryTarget_right_eq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g))) :
    (cofiberBoundaryRightBase f g b).obj (Fin.last (n + 3)) = cofiberBoundaryTarget f g b :=
  (spanBoundaryZeroData_last_obj (sliceUnderUncurry b)).symm

/-- 概要：0 側の既知右辺を標準 cofiber の cochain 座標に移す。
方針：指定余錐の対象と共通終点および次数の等式で線形移送する。
規約：異種等号も下記に公開する。使われ方：六成分線形系の r_0。 -/
def cofiberBoundaryRhs0 {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    Cochain (pushoutCofiber f g) (cofiberBoundaryTarget f g b) (cofiberBoundaryDegree n + 1 + 1) :=
  gradedHomTransport (A := S) (D := Complex S) (cofiberCosliceBoundary_left_apex f g b hb)
    (rfl) (by dsimp only [cofiberBoundaryDegree]; omega)
    ((cofiberBoundaryLeftBase f g b).spanSuffixRhs)

/-- 概要：移送した 0 側右辺は元の境界の右辺と異種等号で一致する。
方針：線形移送の異種等号の公式を使う。
規約：端点と次数の移送を含む。使われ方：微分と合成の整合条件の移送。 -/
lemma cofiberBoundaryRhs0_heq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    HEq (cofiberBoundaryRhs0 f g b hb)
    ((cofiberBoundaryLeftBase f g b).spanSuffixRhs) :=
  gradedHomTransport_heq (A := S) (D := Complex S) (cofiberCosliceBoundary_left_apex f g b hb)
    (rfl) (by dsimp only [cofiberBoundaryDegree]; omega) _

/-- 概要：B 側の既知右辺を標準 cofiber の cochain 座標に移す。
方針：指定余錐の対象と共通終点および次数の等式で線形移送する。
規約：異種等号も下記に公開する。使われ方：六成分線形系の r_B。 -/
def cofiberBoundaryRhsB {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    Cochain (B) (cofiberBoundaryTarget f g b) (cofiberBoundaryDegree n + 1) :=
  gradedHomTransport (A := S) (D := Complex S) (cofiberCosliceBoundary_left_B f g b hb)
    (rfl) rfl
    ((cofiberBoundaryLeftBase f g b).spanOnePrefixRhs
      (spanSecondPrefix n) (spanSecondPrefix_lt_apex n))

/-- 概要：移送した B 側右辺は元の境界の右辺と異種等号で一致する。
方針：線形移送の異種等号の公式を使う。
規約：端点と次数の移送を含む。使われ方：微分と合成の整合条件の移送。 -/
lemma cofiberBoundaryRhsB_heq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    HEq (cofiberBoundaryRhsB f g b hb)
    ((cofiberBoundaryLeftBase f g b).spanOnePrefixRhs
      (spanSecondPrefix n) (spanSecondPrefix_lt_apex n)) :=
  gradedHomTransport_heq (A := S) (D := Complex S) (cofiberCosliceBoundary_left_B f g b hb)
    (rfl) rfl _

/-- 概要：C 側の既知右辺を標準 cofiber の cochain 座標に移す。
方針：指定余錐の対象と共通終点および次数の等式で線形移送する。
規約：異種等号も下記に公開する。使われ方：六成分線形系の r_C。 -/
def cofiberBoundaryRhsC {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    Cochain (C) (cofiberBoundaryTarget f g b) (cofiberBoundaryDegree n + 1) :=
  gradedHomTransport (A := S) (D := Complex S) (cofiberCosliceBoundary_right_C f g b hb)
    (cofiberBoundaryTarget_right_eq f g b) rfl
    ((cofiberBoundaryRightBase f g b).spanOnePrefixRhs
      (spanSecondPrefix n) (spanSecondPrefix_lt_apex n))

/-- 概要：移送した C 側右辺は元の境界の右辺と異種等号で一致する。
方針：線形移送の異種等号の公式を使う。
規約：端点と次数の移送を含む。使われ方：微分と合成の整合条件の移送。 -/
lemma cofiberBoundaryRhsC_heq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    HEq (cofiberBoundaryRhsC f g b hb)
    ((cofiberBoundaryRightBase f g b).spanOnePrefixRhs
      (spanSecondPrefix n) (spanSecondPrefix_lt_apex n)) :=
  gradedHomTransport_heq (A := S) (D := Complex S) (cofiberCosliceBoundary_right_C f g b hb)
    (cofiberBoundaryTarget_right_eq f g b) rfl _

/-- 概要：A 側の既知右辺を標準 cofiber の cochain 座標に移す。
方針：指定余錐の対象と共通終点および次数の等式で線形移送する。
規約：異種等号も下記に公開する。使われ方：六成分線形系の r_A。 -/
def cofiberBoundaryRhsA {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    Cochain (A) (cofiberBoundaryTarget f g b) (cofiberBoundaryDegree n + 1) :=
  gradedHomTransport (A := S) (D := Complex S) (cofiberCosliceBoundary_left_A f g b hb)
    (rfl) rfl
    ((cofiberBoundaryLeftBase f g b).spanOnePrefixRhs 0 (spanApex_pos n))

/-- 概要：移送した A 側右辺は元の境界の右辺と異種等号で一致する。
方針：線形移送の異種等号の公式を使う。
規約：端点と次数の移送を含む。使われ方：微分と合成の整合条件の移送。 -/
lemma cofiberBoundaryRhsA_heq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    HEq (cofiberBoundaryRhsA f g b hb)
    ((cofiberBoundaryLeftBase f g b).spanOnePrefixRhs 0 (spanApex_pos n)) :=
  gradedHomTransport_heq (A := S) (D := Complex S) (cofiberCosliceBoundary_left_A f g b hb)
    (rfl) rfl _

/-- 概要：AB 側の既知右辺を標準 cofiber の cochain 座標に移す。
方針：指定余錐の対象と共通終点および次数の等式で線形移送する。
規約：異種等号も下記に公開する。使われ方：六成分線形系の r_AB。 -/
def cofiberBoundaryRhsAB {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    Cochain (A) (cofiberBoundaryTarget f g b) (cofiberBoundaryDegree n) :=
  gradedHomTransport (A := S) (D := Complex S) (cofiberCosliceBoundary_left_A f g b hb)
    (rfl) (by dsimp only [cofiberBoundaryDegree]; omega)
    ((cofiberBoundaryLeftBase f g b).spanTwoPrefixRhs)

/-- 概要：移送した AB 側右辺は元の境界の右辺と異種等号で一致する。
方針：線形移送の異種等号の公式を使う。
規約：端点と次数の移送を含む。使われ方：微分と合成の整合条件の移送。 -/
lemma cofiberBoundaryRhsAB_heq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    HEq (cofiberBoundaryRhsAB f g b hb)
    ((cofiberBoundaryLeftBase f g b).spanTwoPrefixRhs) :=
  gradedHomTransport_heq (A := S) (D := Complex S) (cofiberCosliceBoundary_left_A f g b hb)
    (rfl) (by dsimp only [cofiberBoundaryDegree]; omega) _

/-- 概要：AC 側の既知右辺を標準 cofiber の cochain 座標に移す。
方針：指定余錐の対象と共通終点および次数の等式で線形移送する。
規約：異種等号も下記に公開する。使われ方：六成分線形系の r_AC。 -/
def cofiberBoundaryRhsAC {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    Cochain (A) (cofiberBoundaryTarget f g b) (cofiberBoundaryDegree n) :=
  gradedHomTransport (A := S) (D := Complex S) (cofiberCosliceBoundary_right_A f g b hb)
    (cofiberBoundaryTarget_right_eq f g b) (by dsimp only [cofiberBoundaryDegree]; omega)
    ((cofiberBoundaryRightBase f g b).spanTwoPrefixRhs)

/-- 概要：移送した AC 側右辺は元の境界の右辺と異種等号で一致する。
方針：線形移送の異種等号の公式を使う。
規約：端点と次数の移送を含む。使われ方：微分と合成の整合条件の移送。 -/
lemma cofiberBoundaryRhsAC_heq {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    HEq (cofiberBoundaryRhsAC f g b hb)
    ((cofiberBoundaryRightBase f g b).spanTwoPrefixRhs) :=
  gradedHomTransport_heq (A := S) (D := Complex S) (cofiberCosliceBoundary_right_A f g b hb)
    (cofiberBoundaryTarget_right_eq f g b) (by dsimp only [cofiberBoundaryDegree]; omega) _

/-- 概要：cofiber Hom 座標へ移した後続右辺は閉じている。
方針：元の境界の後続右辺の閉性を Hom の移送で保つ。
規約：有界性は仮定しない。使われ方：六成分系の最初の整合条件 δr₀=0。 -/
lemma cofiberBoundaryRhs0_closed {n : ℕ} (f : A ⟶ B) (g : A ⟶ C)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceUnder (pushoutSpan (standardCofiberSquare f g)))
    (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (standardCofiberCocone f g)) :
    δ (cofiberBoundaryDegree n + 1 + 1) (cofiberBoundaryDegree n + 1 + 1 + 1)
      (cofiberBoundaryRhs0 f g b hb) = 0 := by
  change differential (D := Complex S) S (cofiberBoundaryRhs0 f g b hb) = 0
  unfold cofiberBoundaryRhs0
  apply gradedHomTransport_closed (A := S) (D := Complex S)
  exact spanBoundaryLeftZeroData_suffixRhs_closed (A := S) (D := Complex S) (n := n)
    (sliceUnderUncurry b)

end SerrePositivity.InfinityCategories
