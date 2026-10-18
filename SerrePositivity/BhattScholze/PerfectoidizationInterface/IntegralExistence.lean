module

public import SerrePositivity.BhattScholze.PerfectoidizationInterface.Interface
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! # 界面を引数とする整代数の perfectoid 化の存在

概要：integral 欄の離散性に、離散時の環の普遍性を適用する。
方針：指定された H⁰ の環と指定単位をそのまま存在の証人に取る。
規約：既存の存在入力を使用せず、S の完備性や有限性を仮定しない。
使われ方：Π2-6 の界面依存版。旧 Inputs の置換は別工程。
-/

@[expose] public section
universe u
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface

/-- 任意の整代数の普遍 perfectoid 化は、界面の integral と universal の欄から従う。 -/
theorem exists_perfectoidization_of_integral
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (F : PerfectoidizationInterfaceE3 R p hR) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), IsPerfectoidization p f := by
  have hInt : (letI : Algebra R (ofAlgebra R S).right := (ofAlgebra R S).hom.hom.toAlgebra
      Algebra.IsIntegral R (ofAlgebra R S).right) := by
    change @Algebra.IsIntegral R S _ _ (algebraMap R S).toAlgebra
    rw [toAlgebra_algebraMap]
    infer_instance
  exact ⟨(F.h0.ringFunctor.obj (ofAlgebra R S)).right, inferInstance,
    (F.h0.unit.app (ofAlgebra R S)).right.hom,
    F.universal (ofAlgebra R S) (F.integral (ofAlgebra R S) hInt).1⟩

end SerrePositivity.BhattScholze.PerfectoidizationInterface
