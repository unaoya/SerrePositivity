module

public import SerrePositivity.CommutativeAlgebra.SupportHeight
public import Mathlib.RingTheory.Localization.Ideal

/-! # Localization away from all least-height support points -/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
namespace Adams
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} {c : ℕ}

/-- Prime avoidance characterizes the ideals disjoint from the chosen denominators. -/
lemma HeightAtLeast.disjoint_complement_iff (h : HeightAtLeast Z c) (I : Ideal R) :
    Disjoint (heightStratumComplement Z c : Set R) (I : Set R) ↔
      ∃ p ∈ heightStratum Z c, I ≤ p.asIdeal := by
  classical
  constructor
  · intro hd
    have hcover : (I : Set R) ⊆ ⋃ p ∈ heightStratum Z c, (p.asIdeal : Set R) := by
      intro s hs
      by_contra hn
      have hm : s ∈ heightStratumComplement Z c := by
        intro p hp hsp
        exact hn (Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hsp⟩⟩)
      exact Set.disjoint_left.mp hd hm hs
    have hex : ∃ p, p ∈ heightStratum Z c := by
      by_contra hn
      have hm : (0 : R) ∈ heightStratumComplement Z c := by
        intro p hp
        exact False.elim (hn ⟨p, hp⟩)
      exact Set.disjoint_left.mp hd hm I.zero_mem
    obtain ⟨p₀, _⟩ := hex
    exact (Ideal.subset_union_prime_finite h.finite_heightStratum p₀ p₀
      (fun p _ _ _ => p.isPrime)).mp hcover
  · rintro ⟨p, hp, hIp⟩
    exact Set.disjoint_left.mpr (fun s hs hI => hs p hp (hIp hI))

variable {B : Type u} [CommRing B] [Algebra R B]
variable [IsLocalization (heightStratumComplement Z c) B]

/-- The localized support consists precisely of points contracting to the height-c stratum. -/
lemma HeightAtLeast.mem_pullback_iff_heightStratum (h : HeightAtLeast Z c)
    (q : PrimeSpectrum B) :
    q ∈ supportPullback (algebraMap R B) Z ↔
      PrimeSpectrum.comap (algebraMap R B) q ∈ heightStratum Z c := by
  constructor
  · intro hq
    let r := PrimeSpectrum.comap (algebraMap R B) q
    have hd : Disjoint (heightStratumComplement Z c : Set R) (r.asIdeal : Set R) :=
      ((IsLocalization.isPrime_iff_isPrime_disjoint (heightStratumComplement Z c) B
        q.asIdeal).mp q.isPrime).2
    obtain ⟨p, hp, hrp⟩ := (h.disjoint_complement_iff r.asIdeal).mp hd
    let : p.asIdeal.FiniteHeight := ⟨Or.inr (hp.2 ▸ ENat.natCast_ne_top c)⟩
    let : r.asIdeal.FiniteHeight := Ideal.finiteHeight_of_le hrp p.isPrime.ne_top
    have he : r = p := by
      apply PrimeSpectrum.ext
      exact Ideal.eq_of_le_of_height_le r.asIdeal hrp (hp.2.le.trans (h r hq))
    change r ∈ heightStratum Z c
    rw [he]
    exact hp
  · exact fun hq => hq.1

/-- The maximal points of the localization are exactly the chosen height-c points. -/
lemma HeightAtLeast.isMax_iff_heightStratum (h : HeightAtLeast Z c) (q : PrimeSpectrum B) :
    IsMax q ↔ PrimeSpectrum.comap (algebraMap R B) q ∈ heightStratum Z c := by
  let e := IsLocalization.primeSpectrumOrderIso (heightStratumComplement Z c) B
  constructor
  · intro hq
    obtain ⟨p, hp, hqp⟩ :=
      (h.disjoint_complement_iff (e q).val.asIdeal).mp (e q).property
    have hdp := (h.disjoint_complement_iff p.asIdeal).mpr ⟨p, hp, le_refl _⟩
    have hle : e q ≤ ⟨p, hdp⟩ := hqp
    have hqle : q ≤ e.symm ⟨p, hdp⟩ := e.le_symm_apply.mpr hle
    have heq : q = e.symm ⟨p, hdp⟩ := le_antisymm hqle (hq hqle)
    change (e q).val ∈ heightStratum Z c
    rw [heq, e.apply_symm_apply]
    exact hp
  · intro hq q' hqq'
    obtain ⟨p, hp, hqp⟩ :=
      (h.disjoint_complement_iff (e q').val.asIdeal).mp (e q').property
    have hqq'' : (e q).val ≤ (e q').val := e.monotone hqq'
    have hle : (e q).val ≤ p := hqq''.trans hqp
    have he : (e q).val = p := heightStratum_eq_of_le hq hp hle
    apply e.le_iff_le.mp
    exact hqp.trans he.symm.le

lemma HeightAtLeast.mem_pullback_iff_isMax (h : HeightAtLeast Z c) (q : PrimeSpectrum B) :
    q ∈ supportPullback (algebraMap R B) Z ↔ IsMax q :=
  (h.mem_pullback_iff_heightStratum q).trans (h.isMax_iff_heightStratum q).symm

lemma HeightAtLeast.mem_pullback_iff_isMaximal (h : HeightAtLeast Z c) (q : PrimeSpectrum B) :
    q ∈ supportPullback (algebraMap R B) Z ↔ q.asIdeal.IsMaximal :=
  (h.mem_pullback_iff_isMax q).trans PrimeSpectrum.isMax_iff

lemma HeightAtLeast.finite_localized_maximal_points (h : HeightAtLeast Z c) :
    {q : PrimeSpectrum B | IsMax q}.Finite := by
  have hi : Function.Injective (PrimeSpectrum.comap (algebraMap R B)) := by
    intro q q' heq
    apply (IsLocalization.primeSpectrumOrderIso (heightStratumComplement Z c) B).injective
    exact Subtype.ext heq
  apply Set.Finite.of_finite_image (f := PrimeSpectrum.comap (algebraMap R B)) ?_ hi.injOn
  apply h.finite_heightStratum.subset
  rintro _ ⟨q, hq, rfl⟩
  exact (h.isMax_iff_heightStratum q).mp hq

/-- Contraction gives a bijection of the finite maximal-point index sets. -/
def HeightAtLeast.localizedMaximalPointsEquiv (h : HeightAtLeast Z c) :
    {q : PrimeSpectrum B // IsMax q} ≃ {p : PrimeSpectrum R // p ∈ heightStratum Z c} :=
  Equiv.ofBijective
    (fun q => ⟨PrimeSpectrum.comap (algebraMap R B) q.val,
      (h.isMax_iff_heightStratum q.val).mp q.property⟩) (by
      let e := IsLocalization.primeSpectrumOrderIso (heightStratumComplement Z c) B
      constructor
      · intro q q' heq
        apply Subtype.ext
        apply e.injective
        have hv : PrimeSpectrum.comap (algebraMap R B) q.val =
            PrimeSpectrum.comap (algebraMap R B) q'.val := congrArg Subtype.val heq
        exact Subtype.ext hv
      · intro p
        let hd := (h.disjoint_complement_iff p.val.asIdeal).mpr ⟨p.val, p.property, le_refl _⟩
        let q := e.symm ⟨p.val, hd⟩
        have heq : PrimeSpectrum.comap (algebraMap R B) q = p.val := by
          change (e (e.symm ⟨p.val, hd⟩)).val = p.val
          rw [e.apply_symm_apply]
        have hq : IsMax q := by
          apply (h.isMax_iff_heightStratum q).mpr
          rw [heq]
          exact p.property
        exact ⟨⟨q, hq⟩, Subtype.ext heq⟩)

end Adams
end SerrePositivity
