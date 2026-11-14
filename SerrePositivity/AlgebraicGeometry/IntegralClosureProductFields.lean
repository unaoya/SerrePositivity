module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Algebra.Polynomial.Monic

/-!
概要：体の積の中の整閉包では、極小素イデアル集合が準コンパクト。
方針：座標の台の冪等元を使って、積の素点の縮約が極小であることを示す。
規約：無限積と空の積を許す。積全体が基底上整であるとは仮定しない。
使われ方：TIC 全体を作らず、Rydh 3.10 に必要な準コンパクトな一般点集合を供給する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v
variable {A : Type u} [CommRing A] {ι : Type v} (K : ι → Type u)
variable [∀ i, Field (K i)] [Algebra A (∀ i, K i)]

/-- 冪等元は X(X-1) を満たすので任意の基底上整。 -/
theorem isIntegral_of_mul_self_eq {S : Type*} [CommRing S] [Algebra A S]
    (e : S) (he : e * e = e) : IsIntegral A e := by
  refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C (1 : A)),
    Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
  change Polynomial.aeval e (Polynomial.X * (Polynomial.X - Polynomial.C (1 : A))) = 0
  simp only [map_mul, map_sub, Polynomial.aeval_X, map_one]
  rw [mul_sub, he, mul_one, sub_self]

/-- 積の中の整閉包の素点への縮約は極小。 -/
theorem comap_integralClosure_productFields_isMinimal
    (P : PrimeSpectrum (∀ i, K i)) :
    (PrimeSpectrum.comap (integralClosure A (∀ i, K i)).val.toRingHom P).asIdeal ∈
      minimalPrimes (integralClosure A (∀ i, K i)) := by
  classical
  let B := integralClosure A (∀ i, K i)
  let f : B →+* (∀ i, K i) := B.val.toRingHom
  refine ⟨⟨(PrimeSpectrum.comap f P).isPrime, bot_le⟩, ?_⟩
  intro Q hQ hQP x hx
  let e : ∀ i, K i := fun i ↦ if (x : ∀ i, K i) i = 0 then 0 else 1
  have he : e * e = e := by
    funext i
    dsimp [e]
    split <;> simp
  let b : B := ⟨e, isIntegral_of_mul_self_eq e he⟩
  have hxe : (x : ∀ i, K i) * (fun i ↦ ((x : ∀ i, K i) i)⁻¹) = e := by
    funext i
    dsimp [e]
    split <;> simp_all
  have hb : e ∈ P.asIdeal := by
    rw [← hxe]
    exact P.asIdeal.mul_mem_right _ hx
  have hsb : 1 - b ∉ (PrimeSpectrum.comap f P).asIdeal := by
    intro hs
    change 1 - e ∈ P.asIdeal at hs
    have h1 := P.asIdeal.add_mem hb hs
    have : (1 : ∀ i, K i) ∈ P.asIdeal := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h1
    exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem P.asIdeal this isUnit_one)
  have hxzero : x * (1 - b) = 0 := by
    apply Subtype.ext
    funext i
    dsimp [b, e]
    split <;> simp_all
  have hmul : x * (1 - b) ∈ Q := hxzero ▸ Q.zero_mem
  exact (hQ.1.mem_or_mem hmul).resolve_right (fun hs ↦ hsb (hQP hs))

/-- 極小素点集合は体の積のスペクトルの連続像であり、準コンパクト。 -/
theorem isCompact_minimalPrimes_integralClosure_productFields :
    IsCompact {q : PrimeSpectrum (integralClosure A (∀ i, K i)) |
      q.asIdeal ∈ minimalPrimes (integralClosure A (∀ i, K i))} := by
  let B := integralClosure A (∀ i, K i)
  let f : B →+* (∀ i, K i) := B.val.toRingHom
  have hd : DenseRange (PrimeSpectrum.comap f) := by
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).mpr
    rw [(RingHom.injective_iff_ker_eq_bot f).mp Subtype.val_injective]
    exact bot_le
  have hr : Set.range (PrimeSpectrum.comap f) =
      {q : PrimeSpectrum B | q.asIdeal ∈ minimalPrimes B} := by
    ext q
    constructor
    · rintro ⟨P, rfl⟩
      exact comap_integralClosure_productFields_isMinimal K P
    · intro hq
      exact ((PrimeSpectrum.denseRange_comap_iff_minimalPrimes f).mp hd) q.asIdeal hq
  rw [← hr]
  exact isCompact_range (PrimeSpectrum.continuous_comap f)

end SerrePositivity.AlgebraicGeometry
