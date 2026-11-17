module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.AicProductArc
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.ProbeComparison
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.ProbeTerms
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.LocalExtensions
public import SerrePositivity.CommutativeAlgebra.ValuationInterval.Zorn
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalTensorComparison
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalRestrictions
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeComparison
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeArrowComparison
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalCoefficientPerfect
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Milnor.ArcCechMilnor

/-!
概要：完全F_p代数の有限族のarc被覆の増大Čech完全性を示す。
方針：付値probe積の正次数の行をP02で処理し、2hとB1の二重Čech比較で消去する。
規約：正本のG-A6-1の型を保つ。BM18 Thm1.7や∞圏の一般の層判定は使わない。
使われ方：2iのP06・B01・B02、BSのG-A6-1の構造層の場合の出口。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity
open SerrePositivity.BhattScholze.Perfectoidization
open scoped TensorProduct Simplicial
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

set_option backward.isDefEq.respectTransparency false

/-- 計画P06：probe積のČechの各正次数へ移した元のarc被覆はČech完全。 -/
theorem probeArc_positiveRows (p : ℕ) [Fact p.Prime]
    {A B : Type u} [CommRing A] [CommRing B] [PerfectRing A p] [PerfectRing B p]
    (hp : (p : A) = 0) (f : A →+* B) (hf : IsArcHom f) :
    ∀ j, 0 < j → Cech.IsCechExact (Cech.changeToTerm
      (Under.mk (CommRingCat.ofHom (Arc.valuationProbeProductMap A)))
      (Under.mk (CommRingCat.ofHom f)) j) := by
  let R := ∀ t : Arc.ValuationProbeIndex A, Arc.ValuationProbe A t
  have hpt (t : Arc.ValuationProbeIndex A) : (p : Arc.ValuationProbe A t) = 0 := by
    rw [← map_natCast (Arc.valuationProbeMap A t), hp, map_zero]
  letI (t : Arc.ValuationProbeIndex A) : CharP (Arc.ValuationProbe A t) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (hpt t)
  letI (t : Arc.ValuationProbeIndex A) : PerfectRing (Arc.ValuationProbe A t) p :=
    (Arc.valuationProbe_aic A t).perfectRing_of_charP p
  letI : PerfectRing R p := perfectRing_pi_of_primeCast_eq_zero p _ hpt
  letI := f.toAlgebra
  letI : Algebra A R := (Arc.valuationProbeProductMap A).toAlgebra
  letI : PerfectRing (R ⊗[A] B) p := perfectTensor_of_primeCast_eq_zero p A R B hp
  have hu := aicValuationProductArc_universalExact p (Arc.ValuationProbe A)
    (Arc.valuationProbe_aic A) hpt (arcBaseChangeHom f (Arc.valuationProbeProductMap A))
    (isArcHom_baseChange f (Arc.valuationProbeProductMap A) hf)
  intro j hj
  cases j with
  | zero => omega
  | succ n =>
    let D := (Cech.underCech (Under.mk (CommRingCat.ofHom
      (Arc.valuationProbeProductMap A)))).right.obj ⦋n⦌
    letI : PerfectRing (Arrow.mk (CommRingCat.ofHom (Arc.valuationProbeProductMap A))).left p :=
      inferInstanceAs (PerfectRing A p)
    letI : PerfectRing (Arrow.mk (CommRingCat.ofHom (Arc.valuationProbeProductMap A))).right p :=
      inferInstanceAs (PerfectRing R p)
    letI : PerfectRing D.right p := Cech.cechConerve_perfectRing p
      (Arrow.mk (CommRingCat.ofHom (Arc.valuationProbeProductMap A))) hp ⦋n⦌
    have hd := hu D.right (probeCechFirstFactor (A := A) n)
    exact (Cech.ringCechExact_iff_of_iso
      (CosimplicialObject.augmentedCechConerve.mapIso (probeChangeToTermIso f n))).mpr hd

/-- 計画B01：完全標数pの環の一射のarc被覆のČech完全性。 -/
theorem cechExact_of_arcHom_perfect (p : ℕ) [Fact p.Prime]
    {A B : Type u} [CommRing A] [CommRing B] [PerfectRing A p] [PerfectRing B p]
    (hp : (p : A) = 0) (f : A →+* B) (hf : IsArcHom f) :
    Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom f)) := by
  letI : PerfectRing (Under.mk (CommRingCat.ofHom f)).right p := ‹PerfectRing B p›
  exact cechExact_of_valuationProbeTests p (bs17VCechInput p)
    (Under.mk (CommRingCat.ofHom f)) hp (probeArc_positiveRows p hp f hf)

/-- 計画B02：有限族の完全F_p代数のarc被覆のČech完全性。G-A6-1と同じ型。 -/
theorem cech_exact_of_arcCover_perfect
    (p : ℕ) [Fact p.Prime] : ArcRouteBGoal.{u} p := by
  intro A _ _ _ ι _ B _ _ _ f hf
  letI : PerfectRing (∀ i, B i) p := perfectRing_pi_of_primeCast_eq_zero p B
    (fun i ↦ CharP.cast_eq_zero (B i) p)
  exact cechExact_of_arcHom_perfect p (CharP.cast_eq_zero A p) (RingHom.pi f)
    ((isArcHom_pi_iff B f).mpr hf)

end SerrePositivity.AlgebraicGeometry.ArcRouteB
