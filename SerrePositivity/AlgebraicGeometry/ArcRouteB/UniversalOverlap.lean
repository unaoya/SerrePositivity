module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.OverlapCoefficientDetection
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeComparison
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeArrowComparison
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalCoefficientPerfect
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Milnor.ArcCechMilnor

/-!
概要：三つの底変換から、全ての完全係数上のČech完全性を検出する。
方針：L01/L02で底変換のArrowを比較し、同じT上のL05へ渡す。
規約：非平坦底変換での完全性の保存は仮定しない。
使われ方：2iのO06、BM18 Proposition 4.8(5)の普遍係数の段。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity
open SerrePositivity.BhattScholze.Perfectoidization
open scoped TensorProduct
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

set_option backward.isDefEq.respectTransparency false

/-- 計画O06：指定した重なりの三つの完全係数から、普遍Čech完全性を得る。 -/
theorem perfectRingCechUniversalExact_of_overlap
    (p : ℕ) [Fact p.Prime] {V B : Type u} [CommRing V] [IsDomain V]
    [ValuationRing V] [CommRing B] [PerfectRing V p] [PerfectRing B p]
    (hp : (p : V) = 0) (f : V →+* B) {a b : PrimeSpectrum V} (h : a ≤ b)
    (hl : PerfectRingCechUniversalExact p (arcBaseChangeHom f
      (algebraMap V (Localization.AtPrime b.asIdeal))))
    (hq : PerfectRingCechUniversalExact p (arcBaseChangeHom f (Ideal.Quotient.mk a.asIdeal)))
    (hr : PerfectRingCechUniversalExact p (arcBaseChangeHom f
      (algebraMap V (ValuationIntervalRing h)))) : PerfectRingCechUniversalExact p f := by
  intro T _ _ k
  letI := f.toAlgebra
  letI := k.toAlgebra
  let BT := Under.mk (CommRingCat.ofHom (arcBaseChangeHom f k))
  letI : PerfectRing BT.right p := perfectTensor_of_primeCast_eq_zero p V T B hp
  have transfer (R : Type u) [CommRing R] [Algebra V R] [PerfectRing R p]
      (hR : PerfectRingCechUniversalExact p (arcBaseChangeHom f (algebraMap V R))) :
      Cech.IsCechExact (Arrow.mk ((CommRingCat.tensorProd (CommRingCat.of T)
        (CommRingCat.of (T ⊗[V] R))).obj BT).hom) := by
    let TR := T ⊗[V] R
    letI : PerfectRing TR p := perfectTensor_of_primeCast_eq_zero p V T R hp
    let iR : R →+* TR := (Algebra.TensorProduct.includeRight : R →ₐ[V] TR).toRingHom
    let iT : T →+* TR := algebraMap T TR
    let u : V →+* TR := algebraMap V TR
    have hiR : iR.comp (algebraMap V R) = u := RingHom.ext
      (fun v ↦ (Algebra.TensorProduct.includeRight : R →ₐ[V] TR).commutes v)
    have hiT : iT.comp k = u := by
      apply RingHom.ext
      intro v
      change algebraMap T TR (algebraMap V T v) = algebraMap V TR v
      exact (IsScalarTower.algebraMap_apply V T TR v).symm
    let eR := arcBaseChangeTransIso f (algebraMap V R) iR u hiR
    let eT := arcBaseChangeTransIso f k iT u hiT
    have hdirect := (Cech.ringCechExact_iff_of_iso
      (CosimplicialObject.augmentedCechConerve.mapIso eR)).mpr (hR TR iR)
    have hbase := (Cech.ringCechExact_iff_of_iso
      (CosimplicialObject.augmentedCechConerve.mapIso eT)).mp hdirect
    let e := arcBaseChangeArrowIso BT TR
    have hnative := (Cech.ringCechExact_iff_of_iso
      (CosimplicialObject.augmentedCechConerve.mapIso e)).mp hbase
    exact hnative
  let L := Localization.AtPrime b.asIdeal
  let Q := V ⧸ a.asIdeal
  let I := ValuationIntervalRing h
  letI : PerfectRing L p := intervalCoefficient_primeLocalization_perfect p hp b
  letI : PerfectRing Q p := intervalCoefficient_primeQuotient_perfect p hp a
  letI : PerfectRing I p := perfectRing_interval h p hp
  exact cechExact_of_overlapTensor_coefficients p BT hp h
    (transfer L hl) (transfer Q hq) (transfer I hr)

end SerrePositivity.AlgebraicGeometry.ArcRouteB
