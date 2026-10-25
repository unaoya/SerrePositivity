module

public import SerrePositivity.BhattScholze.Perfectoidization.SemiperfectoidPerfectoidization
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationFunctor

/-! # B3で選ぶ任意イデアル商の普遍perfectoid化

一般有限代数の存在入力から独立に対象を選ぶBS接続層。
全射性・冪等性・長さの条件は構成に含めない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity

variable (R : Type u) [CommRing R] (I : Ideal R) (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p)

/-- B3の一般全射商の存在で選ぶperfectoid化。 -/
def QuotientPerfectoidization : Type u :=
  (BhattScholze.exists_perfectoidization_of_perfectoid_surjective_quotient hR
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).choose

instance : CommRing (QuotientPerfectoidization R I p hR) :=
  (BhattScholze.exists_perfectoidization_of_perfectoid_surjective_quotient hR
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).choose_spec.choose

/-- 商環からB3の選択対象への標準写像。 -/
def toQuotientPerfectoidization : R ⧸ I →+* QuotientPerfectoidization R I p hR :=
  (BhattScholze.exists_perfectoidization_of_perfectoid_surjective_quotient hR
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).choose_spec.choose_spec.choose

/-- B3で選んだ標準写像の存在・普遍性。 -/
theorem isPerfectoidization_toQuotientPerfectoidization :
    IsPerfectoidization p (toQuotientPerfectoidization R I p hR) :=
  (BhattScholze.exists_perfectoidization_of_perfectoid_surjective_quotient hR
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).choose_spec.choose_spec.choose_spec

instance : Algebra (R ⧸ I) (QuotientPerfectoidization R I p hR) :=
  (toQuotientPerfectoidization R I p hR).toAlgebra

instance : Algebra R (QuotientPerfectoidization R I p hR) :=
  ((toQuotientPerfectoidization R I p hR).comp (Ideal.Quotient.mk I)).toAlgebra

instance : IsScalarTower R (R ⧸ I) (QuotientPerfectoidization R I p hR) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- 商環の作用は選んだ標準写像による。 -/
theorem algebraMap_quotientPerfectoidization :
    algebraMap (R ⧸ I) (QuotientPerfectoidization R I p hR) =
      toQuotientPerfectoidization R I p hR := rfl

/-- 元環の作用は商写像と標準写像の合成による。 -/
theorem algebraMap_base_quotientPerfectoidization :
    algebraMap R (QuotientPerfectoidization R I p hR) =
      (toQuotientPerfectoidization R I p hR).comp (Ideal.Quotient.mk I) := rfl

/-- 零商の選択対象も零環となる。 -/
theorem quotientPerfectoidization_subsingleton [Subsingleton (R ⧸ I)] :
    Subsingleton (QuotientPerfectoidization R I p hR) :=
  (toQuotientPerfectoidization R I p hR).codomain_trivial

/-- pを含む商では、選択したperfectoid化でもpが零になる。 -/
theorem quotientPerfectoidization_natCast_eq_zero (hp : (p : R) ∈ I) :
    (p : QuotientPerfectoidization R I p hR) = 0 := by
  have hq : (p : R ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
  rw [← map_natCast (toQuotientPerfectoidization R I p hR), hq, map_zero]

end SerrePositivity
