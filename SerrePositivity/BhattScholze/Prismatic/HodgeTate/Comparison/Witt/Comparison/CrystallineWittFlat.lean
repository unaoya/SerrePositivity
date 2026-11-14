module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittCoefficients
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittCoefficients

/-!
# 結晶基底から Witt 基底への射の平坦性

## 概要
標準の ℤ_p から Witt 環への係数射は平坦である。

## 方針
非零の p 進整数を単元と p の冪に分け、Witt 環の p 正則性からねじれの無い加群を得る。
離散付値環上のねじれの無い加群の平坦性を使う。

## 規約
係数環は p 正則かつ p 進完備。

## 使われ方
BS 著者版 Theorem 6.4 の結晶の橋の係数変更で、通常テンソルと導来テンソルを照合する。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime] (C : Type u) [CommRing C]
variable (hpC : Function.Injective (fun x : C => (p : C) * x))
variable [IsAdicComplete (Ideal.span {(p : C)}) C]

/-- 標準の結晶基底から Witt 環への係数射は平坦。 -/
theorem crystallineWittBaseMap_flat : (crystallineWittBaseMap.{u} p C hpC).Flat := by
  let k := crystallineBase.{u} p
  let W := WittVector p C
  let f := crystallineWittBaseMap.{u} p C hpC
  let : Algebra k W := f.toAlgebra
  change Module.Flat k W
  let e : k ≃+* PadicInt p := ULift.ringEquiv
  let : IsDomain k := e.injective.isDomain e.toRingHom
  let : IsDiscreteValuationRing k :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm
  have hP : IsSMulRegular W (p : W) := witt_mul_prime_injective p C hpC
  let : Module.IsTorsionFree k W := Module.IsTorsionFree.of_smul_eq_zero (by
    intro a x hx
    by_cases ha : a = 0
    · exact Or.inl ha
    right
    have he : e a ≠ 0 := by
      intro h
      exact ha (e.injective (h.trans e.map_zero.symm))
    let z := e a
    let v := PadicInt.unitCoeff he
    have hu : IsUnit (e.symm (v : PadicInt p)) := v.isUnit.map e.symm.toRingHom
    have hdecomp : a = e.symm (v : PadicInt p) * (p : k) ^ z.valuation := by
      apply e.injective
      simpa only [map_mul, map_pow, map_natCast, e.apply_symm_apply] using
        (PadicInt.unitCoeff_spec he)
    change f a * x = 0 at hx
    rw [hdecomp, map_mul, map_pow, map_natCast, mul_assoc] at hx
    have hx' : (p : W) ^ z.valuation * x = 0 :=
      (hu.map f).mul_left_cancel (by simpa only [mul_zero] using hx)
    apply hP.pow z.valuation
    simpa only [smul_eq_mul, mul_zero] using hx')
  infer_instance

end SerrePositivity.BhattScholze.Prismatic
