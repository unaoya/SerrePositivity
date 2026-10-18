module
public import SerrePositivity.KST.ProExcision.IntegerChainInterval
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Abel

/-!
# 単体的区間から鎖区間への辺の係数

概要：辺を始点と終点の差で数える整数係数と、その境界公式を証明する。
方針：二つの頂点の四通りの実計算と三頂点の望遠鏡相殺を使う。
規約：KST Definition A.3、Construction A.5、非被約な二つの頂点を保持する。
使われ方：ℤΔ¹ の交代面複体から実二項鎖区間への比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision

/-- 概要：二つの頂点を結ぶ辺の整数係数。
方針：終点の整数値から始点の整数値を引く。
規約：KST A.3、通常の増加する辺では0または1。
使われ方：単体的区間の一次鎖の比較。 -/
def integerIntervalWeight (a b : Fin 2) : ℤ := (b : ℕ) - (a : ℕ)

/-- 概要：辺の重みによる標準境界は二つの頂点の差に一致。
方針：二つの頂点の四通りを計算する。
規約：KST A.3、反対向きの対も含む整数加群の等式。
使われ方：区間の比較の一次の微分可換性。 -/
lemma integerIntervalWeight_vertices (a b : Fin 2) :
    integerIntervalWeight a b • (integerIntervalVertex.{u} 1 - integerIntervalVertex 0) =
      integerIntervalVertex b - integerIntervalVertex a := by
  fin_cases a <;> fin_cases b <;> simp [integerIntervalWeight]

/-- 概要：三つの頂点からなる交代境界の辺の重みは零。
方針：各頂点の整数値が二回反対符号で現れることを使う。
規約：KST A.3・A.5。使われ方：区間の比較の二次の微分可換性。 -/
lemma integerIntervalWeight_triangle (a b c : Fin 2) :
    integerIntervalWeight b c - integerIntervalWeight a c + integerIntervalWeight a b = 0 := by
  dsimp only [integerIntervalWeight]
  abel

end SerrePositivity.KST.ProExcision
