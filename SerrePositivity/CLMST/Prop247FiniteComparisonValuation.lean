module

public import SerrePositivity.CommutativeAlgebra.LocalizationComparisonTensorEquiv
public import SerrePositivity.CommutativeAlgebra.IntegralAwayExtension
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Prop 2.4.7：KL の元の有限比較の付値環条件

有限性と元の支持冪条件から、I=(d) を殺さない付値環写像の一意延長を供給する。
局所化判定・整写像の一意延長は既存 API を使用する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.CLMST
set_option backward.isDefEq.respectTransparency false

/-- KL の有限比較の元の支持条件は、原典の付値環条件を満たす。
付値環の rank・p 完備性・離散性・perfectoid 性は要求しない。 -/
theorem prop247_finiteComparison_valuation_extension
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (d : R) (q : A →ₐ[R] B) (hq : q.toRingHom.Finite)
    (hk : ∀ x, q x = 0 → ∃ n : ℕ, d ^ n • x = 0)
    (hc : ∃ n : ℕ, ∀ y : B ⧸ q.toLinearMap.range, d ^ n • y = 0)
    (V : Type v) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra A V]
    (hI : ¬ Ideal.span {algebraMap R A d} ≤ RingHom.ker (algebraMap A V)) :
    ∃! l : B →+* V, l.comp q.toRingHom = algebraMap A V := by
  letI : Algebra A B := q.toRingHom.toAlgebra
  letI : Module.Finite A B := hq
  have hd : algebraMap A V (algebraMap R A d) ≠ 0 := by
    intro hz
    apply hI
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact hz
  obtain ⟨n, hn⟩ := hc
  have hiso := localizationComparison_awayMap_bijective_of_power_bounds d q hk (by
    intro y
    refine ⟨n, ?_⟩
    apply (Submodule.Quotient.mk_eq_zero q.toLinearMap.range).mp
    change q.toLinearMap.range.mkQ (d ^ n • y) = 0
    exact (q.toLinearMap.range.mkQ.map_smul (d ^ n) y).trans (hn _))
  exact existsUnique_valuation_extension_of_integral_away_bijective A B V
    (algebraMap R A d) hd hiso

end SerrePositivity.CLMST
