module

public import SerrePositivity.EInfinity.PowerOperation.MayPrimeFieldZeroSource
public import SerrePositivity.EInfinity.BarrattEccles.Theory.MayPowerOperation

/-!
# Barratt–Eccles 実例の P⁰ の零次の値

May, Proposition 2.3(iii)・BS 著者版 Lemma 8.4(b)。
同じ指定された P⁰ は、零次環の指定比較のもとで p 乗そのものである。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open scoped _root_.Simplicial
open PowerOperation

/-- D79 改訂の零次の欄：同じ P⁰ は指定された π₀ の環で Frobenius。 -/
lemma barrattEcclesPowerOp0_zero (p : ℕ) [Fact p.Prime]
    (x : (CAlg_R (EInfinityPrimeField.{u} p)) _⦋0⦌)
    (a : ((barrattEcclesPi0 (EInfinityPrimeField.{u} p)).obj (SSet.HomotopyCategory.mk x)).right) :
    let e := (barrattEcclesPi0_forget (EInfinityPrimeField.{u} p)).app
      (SSet.HomotopyCategory.mk x)
    (barrattEcclesPowerOp0 p 0).app (SSet.HomotopyCategory.mk x) (e.hom a) = e.hom (a ^ p) :=
  mayPrimeFieldPowerZero_zero p (SSet.HomotopyCategory.mk x) a

end SerrePositivity.EInfinity.BarrattEccles
