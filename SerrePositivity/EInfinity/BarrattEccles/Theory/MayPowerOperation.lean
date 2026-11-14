module

public import SerrePositivity.EInfinity.PowerOperation.MayPrimeFieldPositive
public import SerrePositivity.EInfinity.Interface.PrimeField

/-!
# Barratt–Eccles 実例の May の P⁰

May, Proposition 2.3・BS 著者版 Lemma 8.4。
同じ W→BE の指定比較と ν から、界面の全整数次数の可換群値 NatTrans を供給する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open scoped _root_.Simplicial
open PowerOperation

/-- D79 改訂の本欄：ho(CAlg F_p) 上の全整数次数の May の P⁰。 -/
def barrattEcclesPowerOp0 (p : ℕ) [Fact p.Prime] (n : ℤ) :
    homotopyGroupsOnHo (EInfinityPrimeField.{u} p)
      (cAlgForgetDerived (EInfinityPrimeField.{u} p)) n ⟶
        homotopyGroupsOnHo (EInfinityPrimeField.{u} p)
          (cAlgForgetDerived (EInfinityPrimeField.{u} p)) n :=
  mayPrimeFieldPowerZero p n

/-- 正次数の全成分は零。 -/
lemma barrattEcclesPowerOp0_pos (p : ℕ) [Fact p.Prime]
    (x : (CAlg_R (EInfinityPrimeField.{u} p)) _⦋0⦌) (n : ℤ) (hn : 0 < n) :
    (barrattEcclesPowerOp0 p n).app (SSet.HomotopyCategory.mk x) = 0 := by
  change (mayPrimeFieldPowerZero p n).app (SSet.HomotopyCategory.mk x) = 0
  rw [mayPrimeFieldPowerZero_pos p n hn]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
