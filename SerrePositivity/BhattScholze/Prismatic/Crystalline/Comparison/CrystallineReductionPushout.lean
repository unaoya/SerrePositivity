module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient

/-!
# 可換環の押し出しの mod p

## 概要
可換環の押し出しは p による商と可換。

## 方針
商の脚を持つ任意の余錐では終域の p が零になる。元の押し出しの普遍性で作った射を商に降ろす。

## 規約
余単体的な `quotPow` の指数 1 と同じ商を使う。

## 使われ方
結晶比較の Frobenius に沿う押し出し。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits SerrePositivity.Cosimplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ)

/-- 可換環の p による商。 -/
abbrev crystallineModPrimeRing (R : CommRingCat.{u}) : CommRingCat.{u} :=
  CommRingCat.of (R ⧸ Ideal.span {(p : R) ^ (1 : ℕ)})

/-- p による標準商写像。 -/
def crystallineModPrimeProjection (R : CommRingCat.{u}) : R ⟶ crystallineModPrimeRing p R :=
  CommRingCat.ofHom (Ideal.Quotient.mk _)

/-- 環射が p による商に誘導する射。 -/
def crystallineModPrimeRingMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    crystallineModPrimeRing p R ⟶ crystallineModPrimeRing p S :=
  CommRingCat.ofHom (quotientPowHom f (p : R) (p : S) (map_natCast f.hom p) 1)

@[reassoc] theorem crystallineModPrimeRingMap_comp_projection {R S : CommRingCat.{u}}
    (f : R ⟶ S) :
    crystallineModPrimeProjection p R ≫ crystallineModPrimeRingMap p f =
      f ≫ crystallineModPrimeProjection p S := by
  apply CommRingCat.hom_ext
  rfl

private instance projectionEpi (R : CommRingCat.{u}) :
    Epi (crystallineModPrimeProjection p R) :=
  ConcreteCategory.epi_of_surjective _ Ideal.Quotient.mk_surjective

private theorem prime_in_quotient (R : CommRingCat.{u}) :
    (p : crystallineModPrimeRing p R) = 0 := by
  rw [← map_natCast (crystallineModPrimeProjection p R).hom]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [pow_one]
  exact Ideal.subset_span rfl

local notation "q" => crystallineModPrimeProjection p
local notation "m" => crystallineModPrimeRingMap p
local notation "comm" => crystallineModPrimeRingMap_comp_projection_assoc p

/-- 可換環の押し出しを p で割った正方形も押し出し。 -/
theorem crystallineModPrime_isPushout {R S T U : CommRingCat.{u}}
    {f : R ⟶ S} {g : R ⟶ T} {i : S ⟶ U} {j : T ⟶ U}
    (h : IsPushout f g i j) : IsPushout (m f) (m g) (m i) (m j) := by
  have w : m f ≫ m i = m g ≫ m j := by
    apply (cancel_epi (q R)).mp
    rw [comm f, comm g,
      crystallineModPrimeRingMap_comp_projection p i,
      crystallineModPrimeRingMap_comp_projection p j, h.w_assoc]
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.isColimitAux' _ fun V => ?_)
  have hw : f ≫ q S ≫ V.inl = g ≫ q T ≫ V.inr := by
    rw [← comm f, ← comm g, V.condition]
  let l := h.desc (q S ≫ V.inl) (q T ≫ V.inr) hw
  have hp : (p : V.pt) = 0 := by
    rw [← map_natCast V.inl.hom p, prime_in_quotient, map_zero]
  let lQ : crystallineModPrimeRing p U ⟶ V.pt := CommRingCat.ofHom (Ideal.Quotient.lift _
    l.hom (by
      intro x hx
      rw [pow_one] at hx
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
      rw [map_mul, map_natCast, hp, zero_mul]))
  have hq : q U ≫ lQ = l := by
    apply CommRingCat.hom_ext
    rfl
  refine ⟨lQ, ?_, ?_, ?_⟩
  · apply (cancel_epi (q S)).mp
    change q S ≫ m i ≫ lQ = _
    rw [comm i, hq, h.inl_desc]
  · apply (cancel_epi (q T)).mp
    change q T ≫ m j ≫ lQ = _
    rw [comm j, hq, h.inr_desc]
  · intro x hi hj
    change m i ≫ x = V.inl at hi
    change m j ≫ x = V.inr at hj
    apply (cancel_epi (q U)).mp
    rw [hq]
    apply h.hom_ext
    · rw [h.inl_desc, ← comm i, hi]
    · rw [h.inr_desc, ← comm j, hj]

end SerrePositivity.BhattScholze.Prismatic
