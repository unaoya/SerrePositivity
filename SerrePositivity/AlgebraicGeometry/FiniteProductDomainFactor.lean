module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
概要：有限個の環の積から整域への環準同型は、一つの射影を経由する。
方針：核の素イデアルを有限積の素スペクトルの既存の分解で表し、射影で降ろす。
規約：空の積から非自明な整域への射も自動的に除外される。
使われ方：付値判定における有限族と積への一射の同値。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v w

/-- 有限積から整域への射は、ある成分への射影を経由する。 -/
theorem exists_factor_evalRingHom_of_isDomain
    {ι : Type w} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    {V : Type v} [CommRing V] [IsDomain V] (f : (∀ i, B i) →+* V) :
    ∃ (i : ι) (l : B i →+* V), l.comp (Pi.evalRingHom B i) = f := by
  let p : PrimeSpectrum (∀ i, B i) := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq p
  have hk : RingHom.ker (Pi.evalRingHom B i) ≤ RingHom.ker f := by
    intro x hx
    have hxq : x ∈ (PrimeSpectrum.comap (Pi.evalRingHom B i) q).asIdeal := by
      change (Pi.evalRingHom B i) x ∈ q.asIdeal
      rw [RingHom.mem_ker.mp hx]
      exact q.asIdeal.zero_mem
    simpa only [hq] using hxq
  exact ⟨i, (Pi.evalRingHom B i).liftOfSurjective (Function.surjective_eval i) ⟨f, hk⟩,
    RingHom.liftOfSurjective_comp _ _ _⟩

end SerrePositivity.AlgebraicGeometry
