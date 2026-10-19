module

public import SerrePositivity.EInfinity.IntervalCuts.CochainComposition
public import SerrePositivity.EInfinity.IntervalCuts.CochainUnit
public import SerrePositivity.EInfinity.IntervalCuts.CochainPermutation
public import SerrePositivity.EInfinity.Operad.CoalgebraRestriction
public import SerrePositivity.EInfinity.TableReduction.OperadMap

/-!
# 正規化区間の具体的な χ・E 余代数

概要：Berger–Fresse §2.2・§3.1 の区間切断作用から実際の余代数構造を得る。
方針：全整数複体射の単位・等変性・全部分合成則を束ね、一般 TR に沿って制限する。
規約：任意の可換環、nullary を含み、モデル構造や区間条件を仮定しない。
使われ方：端点・収縮・境界包含を備えた E-coalgebra 区間の底の余代数。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory

variable (A : Type u) [CommRing A]

/-- 概要：実際の区間切断作用による χ-coalgebra（BF §2.2・§3.1）。
方針：具体的な余作用射と証明済みの全 arity の三公理を束ねる。
規約：底は正規化 Δ¹ の整数コチェイン複体。
使われ方：TR による E への制限と、具体区間条件の検証。 -/
def surjectionCoalgebra : (Surjection.operad A).Coalgebra where
  carrier := interval A
  coaction := cochainAction A
  equivariance := cochainAction_equivariance A
  unit_coaction := cochainAction_unit A
  comp_coaction := cochainAction_operad_comp A

/-- 概要：一般の table reduction を制限した正規化区間の E-coalgebra（BF §3.1）。
方針：実際のオペラッド射 E → χ に沿って具体的な χ-coalgebra を制限する。
規約：底の複体は同じ正規化区間で、全 arity・全次数の TR を使う。
使われ方：E-coalgebra 区間の具体的な余代数構造。 -/
def barrattEcclesCoalgebra : (BarrattEccles.operad A).Coalgebra :=
  Operad.restrictCoalgebraObj (TableReduction.operadMap A) (surjectionCoalgebra A)

/-- 概要：制限後の区間余作用は実際の TR と切断作用の合成（BF §3.1）。
方針：余代数制限の余作用成分を評価する。
規約：全 arity、同じ正規化区間と同じ出力テンソル。
使われ方：端点・収縮の余代数射性を具体的に検証する。 -/
lemma barrattEcclesCoalgebra_coaction (n : ℕ) :
    (barrattEcclesCoalgebra A).coaction n =
      ((TableReduction.operadMap A).map.app (FiniteBijection.of n) ▷ interval A) ≫
        cochainAction A n := rfl

end SerrePositivity.EInfinity.IntervalCuts
