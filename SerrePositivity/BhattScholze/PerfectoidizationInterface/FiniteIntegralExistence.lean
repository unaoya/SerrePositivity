module

public import SerrePositivity.BhattScholze.PerfectoidizationInterface.IntegralPerfectoidization
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationCompletion
public import Mathlib.RingTheory.Finiteness.Basic

/-! # 整代数の原典入力から有限版と完備化版への接続

有限代数の整性を確認して原典の普遍 perfectoid 化を適用する。
完備化の場合には、同じ目標環と写像の一意延長を用いて普遍性を移す。
新しい対象を選び直さず、古典完備化と導来完備化の同値も仮定しない。
-/

@[expose] public section
universe u
namespace SerrePositivity.BhattScholze

/-- 有限代数の存在主張は、整代数についての原典の存在入力への適用である。
有限表示性はこの導出には不要である。 -/
theorem exists_perfectoidization_of_finite
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), IsPerfectoidization p f :=
  Inputs.exists_perfectoidization_of_integral R S p hR

/-- 整代数の古典 p 進完備化にも、同じ環を使って普遍 perfectoid 化を与えられる。
元環の普遍性と完備化への一意延長からの系であり、prismatic perfection 本体の定義ではない。 -/
theorem exists_perfectoidization_of_completed_integral
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) :
    ∃ (C : Type u) (_ : CommRing C)
      (f : AdicCompletion (Ideal.span {(p : S)}) S →+* C), IsPerfectoidization p f := by
  obtain ⟨C, hC, f, hf⟩ := Inputs.exists_perfectoidization_of_integral R S p hR
  exact ⟨C, hC, hf.completionMap p, hf.to_completion p⟩

end SerrePositivity.BhattScholze
