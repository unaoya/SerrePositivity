module

public import SerrePositivity.BhattScholze.Delta.Free.CrystallineTensorRegularity
public import SerrePositivity.BhattScholze.Delta.DividedPower.PDivision.PDivisionCompletion

/-!
# 完備 p 除算の mod p

## 概要
p 正則な δ 除算環では、ねじれ除去と完備化を通っても mod p は同じ環になる。

## 方針
ねじれ除去の比較と、完備化の第 1 射影の核の計算を合成する。

## 規約
古典的完備化を用いる。

## 使われ方
結晶比較の Frobenius 押し出しを完備模型へ移す。
-/

public noncomputable section

universe u v

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
    {σ : Type v} (D : DeltaStructure p R) (a : σ → R)

local notation "B₀" => DeltaAdjoinDivision D (p : R) a
local notation "B" => DeltaDivisionTorsionQuotient D (p : R) a
local notation "C" => ClassicalDeltaDivisionCompletion D (p : R) a
local notation "I" => deltaDivisionAdicIdeal D (p : R) a

private theorem divisionCompletion_ker :
    RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom = Ideal.span {(p : C)} := by
  have h := AdicCompletion.ker_evalOneₐ_eq_map I (deltaDivisionAdicIdeal_fg D (p : R) a)
  refine h.trans ((congrArg (fun J : Ideal B => J.map (algebraMap B C))
    (deltaPDivisionAdicIdeal_eq_span_p D a)).trans ?_)
  rw [Ideal.map_span, Set.image_singleton]
  exact congrArg (fun x : C => Ideal.span {x}) (map_natCast (algebraMap B C) p)

/-- 完備 p 除算環の剰余と、添加の関係式だけを課した環の剰余を同一視する。 -/
def crystallineDivisionCompletionModPrimeEquiv (hp : IsSMulRegular B₀ (p : B₀)) :
    (C ⧸ Ideal.span {(p : C)}) ≃+* (B₀ ⧸ Ideal.span {(p : B₀)}) := by
  let e := deltaDivisionTorsionEquivOfPrimeRegular D a hp
  have he : Ideal.span {(p : B₀)} = (I).map e.toRingHom := by
    rw [deltaPDivisionAdicIdeal_eq_span_p, Ideal.map_span, Set.image_singleton,
      RingEquiv.toRingHom_eq_coe, map_natCast]
  exact (Ideal.quotEquivOfEq (divisionCompletion_ker D a).symm).trans
    ((RingHom.quotientKerEquivOfSurjective (AdicCompletion.evalOneₐ_surjective I)).trans
      (Ideal.quotientEquiv I _ e he))

/-- 剰余比較は完備化へ入れる前の元の像を保つ。 -/
theorem crystallineDivisionCompletionModPrimeEquiv_unit (hp : IsSMulRegular B₀ (p : B₀))
    (x : B₀) :
    crystallineDivisionCompletionModPrimeEquiv D a hp
      (Ideal.Quotient.mk _ (algebraMap B C (Ideal.Quotient.mk _ x))) =
      Ideal.Quotient.mk _ x := by
  let q : B₀ →+* B := Ideal.Quotient.mk _
  let e := deltaDivisionTorsionEquivOfPrimeRegular D a hp
  unfold crystallineDivisionCompletionModPrimeEquiv
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingEquiv.trans_apply]
  change Ideal.Quotient.mk _ (e ((q) x)) = _
  exact congrArg (Ideal.Quotient.mk _) (deltaDivisionTorsionEquivOfPrimeRegular_mk D a hp x)

end SerrePositivity.BhattScholze.Prismatic
