module

public import SerrePositivity.KST.DerivedBlowup.Charts
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
概要：KST Def3.1・Lemma3.6 の普遍 blowup の i チャート ℤ[T_i,S_j] を構成する。
方針：none を T_i、some j を S_j とする多項式環を使う。
規約：基底環は ℤ[T_j]、対象添字は任意で有限性をまだ使わない。
使われ方：A への導来底変更の Koszul 表示と射影空間上の O(−1) の全空間との比較。
-/

@[expose] public noncomputable section

universe v

namespace SerrePositivity.KST.DerivedBlowup

variable {I : Type v} [DecidableEq I]

/-- 概要：普遍 blowup の基底 ℤ[T_j]。方針：全同次座標を自由変数にする。
規約：KST Def3.1。使われ方：普遍チャートへの構造射の始域。 -/
abbrev UniversalBase (I : Type v) := MvPolynomial I ℤ

/-- 概要：普遍 i チャートの ℤ[T_i,S_j]。方針：radial 座標と比座標を分ける。
規約：KST §3.1、j≠i。使われ方：導来底変更前の正則なチャート模型。 -/
abbrev UniversalChart (i : I) := MvPolynomial (Option (ChartIndex i)) ℤ

/-- 概要：射影空間のチャートから全空間への環射。
方針：比座標を some に名前変更する。規約：Thomason Lemme2.3 の射影空間経路。
使われ方：普遍 blowup を O(−1) の全空間として扱う座標環。 -/
def projectiveChartInclusion (i : I) : ChartRing ℤ i →ₐ[ℤ] UniversalChart i :=
  MvPolynomial.rename some

/-- 概要：普遍チャートの radial 座標 T_i。方針：none に対応する変数。
規約：KST Def3.1。使われ方：基底の T_j=T_i S_j の計算。 -/
def radialCoordinate (i : I) : UniversalChart i := MvPolynomial.X none

/-- 概要：普遍全空間での比座標。方針：射影チャートの規格化座標の像。
規約：KST §3.1、i 番目は1。使われ方：普遍構造射と重なり。 -/
def universalRatio (i j : I) : UniversalChart i :=
  projectiveChartInclusion i (chartCoordinate ℤ i j)

@[simp] theorem universalRatio_self (i : I) : universalRatio i i = 1 := by
  simp [universalRatio]

@[simp] theorem universalRatio_other (i : I) (j : ChartIndex i) :
    universalRatio i j.val = MvPolynomial.X (some j) := by
  simp [universalRatio, projectiveChartInclusion]

/-- 概要：普遍 blowup のチャート構造射。方針：T_j を T_i S_j に送る。
規約：KST Def3.1、スキームと逆向きの環射。使われ方：任意の a_j への底変更。 -/
def universalBaseMap (i : I) : UniversalBase I →ₐ[ℤ] UniversalChart i :=
  MvPolynomial.aeval (fun j => radialCoordinate i * universalRatio i j)

/-- 概要：普遍構造射の各変数の像。方針：aeval の生成元計算。
規約：KST Def3.1 のチャート。使われ方：導来底変更で a_iS_j−a_j を得る。 -/
@[simp] theorem universalBaseMap_X (i j : I) :
    universalBaseMap i (MvPolynomial.X j) = radialCoordinate i * universalRatio i j := by
  exact MvPolynomial.aeval_X _ _

/-- 概要：普遍構造射は pivot を radial 座標に送る。方針：S_i=1。
規約：KST Def3.1。使われ方：基底変更後の T_i=a_i の消去。 -/
@[simp] theorem universalBaseMap_pivot (i : I) :
    universalBaseMap i (MvPolynomial.X i) = radialCoordinate i := by
  simp

/-- 概要：普遍チャート上で全ての blowup 二項関係式が零。
方針：T_j=T_i S_j を代入し可換性で整理する。
規約：KST Lemma3.6 の普遍表示。使われ方：古典 Proj チャートとの環射の比較。 -/
theorem universalMinor_zero (i j k : I) :
    universalBaseMap i (MvPolynomial.X j) * universalRatio i k -
      universalBaseMap i (MvPolynomial.X k) * universalRatio i j = 0 := by
  simp only [universalBaseMap_X]
  ring

end SerrePositivity.KST.DerivedBlowup
