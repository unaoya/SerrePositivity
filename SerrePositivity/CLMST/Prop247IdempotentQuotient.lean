module

public import SerrePositivity.CommutativeAlgebra.IdempotentAnnihilator
public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedPerfectoidQuotient
public import SerrePositivity.BhattScholze.CompatibleRootFamilyCompletionPerfectoid

/-! # Prop 2.4.7：perfectoid 環の冪等元による直因子

冪等元を定数の両立 p 冪根族と見て、既存の根族完備商定理を適用する。
商の古典的完備性は補冪等元の annihilator 商の既存 API から得る。
絶対整閉性や一般 integral perfectoid 化の存在引用は使用しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
set_option backward.isDefEq.respectTransparency false

/-- 任意の perfectoid 環の冪等元による商は perfectoid である。零環も含む。 -/
theorem prop247_isIntegralPerfectoid_idempotent_quotient
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (e : R) (he : IsIdempotentElem e) :
    IsIntegralPerfectoid (R ⧸ Ideal.span {e}) p := by
  letI := hR.isAdicComplete R p
  have hc := annihilatorPrincipalQuotient_isAdicComplete R p (1 - e)
  rw [annihilator_span_one_sub_of_idempotent R e he] at hc
  letI := hc
  let ρ : R → ℕ → R := fun _ _ => e
  have hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n := fun _ _ =>
    he.pow_eq (Fact.out : p.Prime).ne_zero
  have hK : compatibleRootFamilyIdeal ρ = Ideal.span {e} := by
    simp only [compatibleRootFamilyIdeal, ρ, Set.range_const]
  have hP := BhattScholze.compatibleRootFamilyCompletion_isIntegralPerfectoid hR ρ hρ
  change IsIntegralPerfectoid
    (AdicCompletion (Ideal.span {(p : R ⧸ compatibleRootFamilyIdeal ρ)})
      (R ⧸ compatibleRootFamilyIdeal ρ)) p at hP
  rw [hK] at hP
  let eqv : (R ⧸ Ideal.span {e}) ≃+*
      AdicCompletion (Ideal.span {(p : R ⧸ Ideal.span {e})}) (R ⧸ Ideal.span {e}) :=
    RingEquiv.ofBijective (algebraMap _ _) (by
      change Function.Bijective (AdicCompletion.of _ _)
      exact AdicCompletion.of_bijective _ _)
  exact BhattScholze.isIntegralPerfectoid_of_ringEquiv p eqv.symm hP

end SerrePositivity.CLMST
