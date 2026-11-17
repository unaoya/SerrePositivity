module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalRestrictions
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalPoints
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.EndpointSections

/-!
概要：完全化した有限表示arc模型について、良い区間を左右へ非自明に延長する。
方針：端点が隣接する場合はrank≤1、そうでなければ剰余体の点を有限表示で区間へ降ろす。
規約：元の模型と区間を保ち、左右の向きを別々に検証する。
使われ方：2iのI09・I10、BM18 Proposition 4.8(3),(4)とLemma 4.7の局所延長。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
open SerrePositivity
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

set_option backward.isDefEq.respectTransparency false

/-- 計画I09：指定された端点からの非退化区間への局所延長。 -/
theorem goodArcInterval_right (p : ℕ) [Fact p.Prime]
    {V C : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing C]
    [Algebra V C] [Algebra.FinitePresentation V C] [PerfectRing V p]
    (hV : IsAbsolutelyIntegrallyClosed V) (hp : (p : V) = 0)
    (hf : IsArcHom (perfectedAlgebraUnit p V C hp)) {a b : PrimeSpectrum V}
    (hab : a < b) : ∃ c, a < c ∧ GoodArcInterval p (perfectedAlgebraUnit p V C hp) a c := by
  classical
  letI : LinearOrder (PrimeSpectrum V) :=
    LinearOrder.lift' PrimeSpectrum.asIdeal (fun _ _ h ↦ PrimeSpectrum.ext h)
  let hC : (p : C) = 0 := by rw [← map_natCast (algebraMap V C), hp, map_zero]
  let CP := FrobeniusDirectLimit C p (Fact.out : p.Prime) hC
  letI : PerfectRing CP p := frobeniusDirectLimit_perfectRing p C hC
  by_cases hdense : ∀ c : PrimeSpectrum V, a < c → ∃ d, a < d ∧ d < c
  · obtain ⟨g, _⟩ := exists_fp_residue_point_of_perfectedArc p (V := V) (C := C) hV hp hf a
    obtain ⟨c, hac, ⟨s⟩⟩ := exists_right_interval_fp_section a ⟨b, hab⟩ hdense g
    letI : PerfectRing (ValuationIntervalRing hac.le) p := perfectRing_interval hac.le p hp
    refine ⟨c, hac, ?_⟩
    intro h
    exact perfectedAlgebraUnit_universalExact_of_section p hp s
  · push_neg at hdense
    obtain ⟨c, hac, hmin⟩ := hdense
    have hgap : ∀ d : PrimeSpectrum V, a ≤ d → d ≤ c → d = a ∨ d = c := by
      intro d had hdc
      rcases eq_or_lt_of_le had with he | had'
      · exact Or.inl he.symm
      · exact Or.inr (le_antisymm hdc (hmin d had'))
    exact ⟨c, hac, goodArcInterval_of_rank_le_one p (B := CP) hp
      (perfectedAlgebraUnit p V C hp) hf hac.le
      (intervalRing_krullDim_le_one_of_no_prime_between hac.le hgap)⟩

/-- 計画I10：指定された端点からの非退化区間への局所延長。 -/
theorem goodArcInterval_left (p : ℕ) [Fact p.Prime]
    {V C : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing C]
    [Algebra V C] [Algebra.FinitePresentation V C] [PerfectRing V p]
    (hV : IsAbsolutelyIntegrallyClosed V) (hp : (p : V) = 0)
    (hf : IsArcHom (perfectedAlgebraUnit p V C hp)) {a b : PrimeSpectrum V}
    (hab : a < b) : ∃ c, c < b ∧ GoodArcInterval p (perfectedAlgebraUnit p V C hp) c b := by
  classical
  letI : LinearOrder (PrimeSpectrum V) :=
    LinearOrder.lift' PrimeSpectrum.asIdeal (fun _ _ h ↦ PrimeSpectrum.ext h)
  let hC : (p : C) = 0 := by rw [← map_natCast (algebraMap V C), hp, map_zero]
  let CP := FrobeniusDirectLimit C p (Fact.out : p.Prime) hC
  letI : PerfectRing CP p := frobeniusDirectLimit_perfectRing p C hC
  by_cases hdense : ∀ c : PrimeSpectrum V, c < b → ∃ d, c < d ∧ d < b
  · obtain ⟨g, _⟩ := exists_fp_residue_point_of_perfectedArc p (V := V) (C := C) hV hp hf b
    obtain ⟨c, hcb, ⟨s⟩⟩ := exists_left_interval_fp_section b ⟨a, hab⟩ hdense g
    letI : PerfectRing (ValuationIntervalRing hcb.le) p := perfectRing_interval hcb.le p hp
    refine ⟨c, hcb, ?_⟩
    intro h
    exact perfectedAlgebraUnit_universalExact_of_section p hp s
  · push_neg at hdense
    obtain ⟨c, hcb, hmax⟩ := hdense
    have hgap : ∀ d : PrimeSpectrum V, c ≤ d → d ≤ b → d = c ∨ d = b := by
      intro d hcd hdb
      rcases lt_or_eq_of_le hdb with hdb' | he
      · exact Or.inl (le_antisymm (le_of_not_gt (fun hcd' ↦ hdb'.not_ge (hmax d hcd'))) hcd)
      · exact Or.inr he
    exact ⟨c, hcb, goodArcInterval_of_rank_le_one p (B := CP) hp
      (perfectedAlgebraUnit p V C hp) hf hcb.le
      (intervalRing_krullDim_le_one_of_no_prime_between hcb.le hgap)⟩

end SerrePositivity.AlgebraicGeometry.ArcRouteB
