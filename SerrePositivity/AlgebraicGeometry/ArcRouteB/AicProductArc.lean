module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.UniversalUltraproduct
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.AicValuationArc
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeComparison
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeArrowComparison
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalCoefficientPerfect
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Milnor.ArcCechMilnor

/-!
概要：絶対整閉な完全付値環の積の上のarc被覆の普遍Čech完全性。
方針：既存の超積の付値環・絶対整閉性とI12を、P01へ渡す。
規約：空の積も含め、元の被覆と指定した超積への底変換を保つ。
使われ方：2iのP02、BM18 Proposition 4.8とLemma 3.27。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity
open SerrePositivity.BhattScholze.Perfectoidization
open scoped TensorProduct
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

set_option backward.isDefEq.respectTransparency false

/-- 計画P02：絶対整閉付値環の任意の積上で、arc被覆は普遍Čech完全。 -/
theorem aicValuationProductArc_universalExact
    (p : ℕ) [Fact p.Prime] {ι : Type u} (V : ι → Type u)
    [∀ i, CommRing (V i)] [∀ i, IsDomain (V i)] [∀ i, ValuationRing (V i)]
    [∀ i, PerfectRing (V i) p] (hV : ∀ i, IsAbsolutelyIntegrallyClosed (V i))
    (hp : ∀ i, (p : V i) = 0) {B : Type u} [CommRing B] [PerfectRing B p]
    (f : (∀ i, V i) →+* B) (hf : IsArcHom f) : PerfectRingCechUniversalExact p f := by
  let A := ∀ i, V i
  have hA : (p : A) = 0 := funext hp
  letI : PerfectRing A p := perfectRing_pi_of_primeCast_eq_zero p V hp
  letI (U : Ultrafilter ι) : PerfectRing (RingUltraproduct V U) p :=
    perfectRing_ultraproduct_of_aic V U hV p hA
  apply perfectRingCechUniversalExact_of_ultraproducts p V hA f
  intro U
  let D := RingUltraproduct V U
  letI : ValuationRing D := valuationRing_ultraproduct V U
  letI := f.toAlgebra
  letI : PerfectRing (D ⊗[A] B) p := perfectTensor_of_primeCast_eq_zero p A D B hA
  have hD : (p : D) = 0 := by rw [← map_natCast (algebraMap A D), hA, map_zero]
  exact aicValuationArc_universalExact p (aic_ultraproduct V U hV) hD
    (arcBaseChangeHom f (algebraMap A D)) (isArcHom_baseChange f (algebraMap A D) hf)

end SerrePositivity.AlgebraicGeometry.ArcRouteB
