module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCover
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PadicIntMap
public import SerrePositivity.BhattScholze.Prism.Basic.UniversalOriented
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RingHom.Flat
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase

/-!
# 特定の普遍結晶被覆への標準 Zp 係数射

## 概要
普遍向き付き prism の Construction 6.1 の結晶被覆へ、既存の標準 Zp 作用を入れる。

## 方針
既存の p 完備環への Zp 射の一意性から Frobenius の両立を得て、p 正則性で δ の両立へ戻す。

## 規約
ここでは一般の結晶 Hodge–Tate 比較は主張しない。二つの選択生成元はどちらも p である。

## 使われ方
BS 著者版 Proposition 6.2 の普遍基底の結晶入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DerivedCompletion
open SerrePositivity.BhattScholze.Perfectoidization.Derived
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
attribute [local instance] HasDerivedCategory.standard
variable (p : ℕ) [Fact p.Prime]

private theorem padicMap_flat_of_p_regular {T : Type u} [CommRing T]
    (f : PadicInt p →+* T) (hp : Function.Injective (fun x : T => (p : T) * x)) : f.Flat := by
  letI := f.toAlgebra
  haveI : Module.IsTorsionFree (PadicInt p) T := by
    constructor
    intro r hr
    have hr0 : r ≠ 0 := hr.ne_zero
    change Function.Injective (fun x : T => f r * x)
    rw [PadicInt.unitCoeff_spec hr0, map_mul, map_pow, map_natCast]
    have hu : IsSMulRegular T (f (PadicInt.unitCoeff hr0 : PadicInt p)) :=
      IsUnit.isSMulRegular T ((PadicInt.unitCoeff hr0).isUnit.map f)
    exact hu.mul ((show IsSMulRegular T (p : T) from hp).pow r.valuation)
  change Module.Flat (PadicInt p) T
  infer_instance

/-- 特定の普遍結晶被覆への元の標準 p 進係数射。 -/
def coefficientMap : crystallineBase.{u} p →+* (Construction61.crystallineCoverRing (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p)) :=
  (arcPadicIntMap p (Construction61.crystallineCoverRing (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p)) (Construction61.crystallineCover_complete_p (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p))).comp
    ULift.ringEquiv.toRingHom

/-- この特定の係数射の平坦性は、被覆の p 正則性から従う。 -/
theorem coefficientMap_flat : (coefficientMap.{u} p).Flat := by
  have h := padicMap_flat_of_p_regular p
    (arcPadicIntMap p (Construction61.crystallineCoverRing (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p)) (Construction61.crystallineCover_complete_p (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p)))
    (Construction61.crystallineCover_p_regular (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p))
  have he : (ULift.ringEquiv : crystallineBase.{u} p ≃+* PadicInt p).toRingHom.Flat :=
    RingHom.Flat.of_bijective ULift.ringEquiv.bijective
  exact he.comp h

/-- 標準 p 進係数は、被覆の元の Frobenius によって固定される。 -/
theorem coefficientMap_frobenius (x : crystallineBase.{u} p) :
    (Construction61.coverDelta (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p)).frobeniusLift (coefficientMap.{u} p x) = coefficientMap.{u} p x := by
  have h := arcPadicIntMap_unique p (Construction61.crystallineCoverRing (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p)) (Construction61.crystallineCover_complete_p (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p))
    ((Construction61.coverDelta (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p)).frobeniusLift.comp
      (arcPadicIntMap p (Construction61.crystallineCoverRing (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p)) (Construction61.crystallineCover_complete_p (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p))))
  exact RingHom.congr_fun h (ULift.ringEquiv x)

-- 普遍被覆の局所化商と完備化の δ 構造を比較するため、展開の予算を増やす。
set_option maxHeartbeats 1600000 in
/-- 元の二つの δ 構造との両立。 -/
theorem coefficientMap_isDeltaHom :
    (crystallineBasePrism.{u} p).deltaStructure.IsDeltaHom
      (Construction61.crystallineCover (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p)).deltaStructure (coefficientMap.{u} p) := by
  apply DeltaStructure.isDeltaHom_of_map_frobeniusLift _ (Construction61.crystallineCover_p_regular (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p))
  intro x
  change coefficientMap.{u} p ((crystallineBaseDelta p).frobeniusLift x) =
    (Construction61.coverDelta (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p)).frobeniusLift (coefficientMap.{u} p x)
  rw [crystallineBaseDelta_frobenius, RingHom.id_apply]
  exact (coefficientMap_frobenius.{u} p x).symm

-- 同じ局所化商の型を持つ ideal の証明と prism 構造を照合する。
set_option maxHeartbeats 1600000 in
/-- 特定の普遍結晶被覆への、選択生成元 p を保つ prism 射。 -/
def coefficientHom : OrientedPrism.Hom (crystallineBasePrism.{u} p) (Construction61.crystallineCover (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p)) where
  toRingHom := coefficientMap.{u} p
  map_delta := coefficientMap_isDeltaHom.{u} p
  ideal_le := by
    change Ideal.span {(crystallineBasePrism.{u} p).generator} ≤ _
    rw [Ideal.span_singleton_le_iff_mem, crystallineBase_generator]
    change coefficientMap.{u} p (p : crystallineBase.{u} p) ∈ Ideal.span {(p : (Construction61.crystallineCoverRing (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p)))}
    exact (map_natCast (coefficientMap.{u} p) p).symm ▸ Ideal.mem_span_singleton_self _

/-- この特定の係数射は、選択生成元を単元 1 の係数で保つ。 -/
theorem coefficientHom_generator :
    (coefficientHom.{u} p).toRingHom (crystallineBasePrism.{u} p).generator =
      (Construction61.crystallineCover (SerrePositivity.BhattScholze.universalOrientedPrism.{u} p)).generator := by
  change coefficientMap.{u} p (crystallineBasePrism.{u} p).generator = _
  rw [crystallineBase_generator, Construction61.crystallineCover_generator]
  exact map_natCast (coefficientMap.{u} p) p

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
