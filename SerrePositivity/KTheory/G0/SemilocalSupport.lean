module

public import SerrePositivity.CommutativeAlgebra.Support.Closed
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Localization.Ideal
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Dimension

/-! # 台の高さと半局所化

## 概要

有限加群の台の点の高さの上界と、高さが最小の台の点の有限集合を与え、それらの点のすべての外での局所化を作る。

## 方針

台は有限個の極小素イデアルの閉包の和なので、高さが最小の点は有限個。

## 規約

CommutativeAlgebra から受け入れた（SupportHeight・SemilocalSupport・ModuleSupportHeight、refactor-plan §6.2.1）。

## 使われ方

KTheory/Adams の半局所化の純粋な重み。
-/

@[expose] public noncomputable section

universe u

section SupportHeightPart

namespace SerrePositivity
namespace Adams
variable {R : Type u} [CommRing R]

/-- Height bounds retain the extended-natural value of prime height. -/
def HeightAtLeast (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (c : ℕ) : Prop :=
  ∀ p ∈ Z, (c : ℕ∞) ≤ p.asIdeal.height

def heightStratum (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (c : ℕ) :
    Set (PrimeSpectrum R) := {p | p ∈ Z ∧ p.asIdeal.height = (c : ℕ∞)}

lemma HeightAtLeast.mono {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} {c : ℕ}
    (h : HeightAtLeast Z c) (hW : W ≤ Z) : HeightAtLeast W c :=
  fun p hp => h p (hW hp)

lemma heightAtLeast_zero (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    HeightAtLeast Z 0 := fun _ _ => bot_le

lemma HeightAtLeast.ideal_height {I : Ideal R} {c : ℕ}
    (h : HeightAtLeast (supportZeroLocus I) c) : (c : ℕ∞) ≤ I.height := by
  rw [Ideal.height_eq_inf_minimalPrimes]
  refine le_iInf₂ fun J hJ => ?_
  let p : PrimeSpectrum R := ⟨J, hJ.isPrime⟩
  exact h p hJ.le

lemma HeightAtLeast.mem_minimalPrimes {I : Ideal R} {c : ℕ}
    (h : HeightAtLeast (supportZeroLocus I) c) {p : PrimeSpectrum R}
    (hp : p ∈ heightStratum (supportZeroLocus I) c) : p.asIdeal ∈ I.minimalPrimes := by
  let : p.asIdeal.FiniteHeight := ⟨Or.inr (hp.2 ▸ ENat.natCast_ne_top c)⟩
  exact Ideal.mem_minimalPrimes_of_height_le hp.1 (hp.2.le.trans h.ideal_height)

lemma HeightAtLeast.finite_heightStratum [IsNoetherianRing R]
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} {c : ℕ} (h : HeightAtLeast Z c) :
    (heightStratum Z c).Finite := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp Z.isClosed
  have hZ : Z = supportZeroLocus I := SetLike.coe_injective hI
  subst Z
  have hs : PrimeSpectrum.asIdeal '' heightStratum (supportZeroLocus I) c ⊆ I.minimalPrimes := by
    rintro _ ⟨p, hp, rfl⟩
    exact h.mem_minimalPrimes hp
  exact Set.Finite.of_finite_image ((I.finite_minimalPrimes_of_isNoetherianRing R).subset hs)
    (fun _ _ _ _ h => PrimeSpectrum.ext h)

lemma heightStratum_eq_of_le {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {c : ℕ} {p q : PrimeSpectrum R}
    (hp : p ∈ heightStratum Z c) (hq : q ∈ heightStratum Z c) (hpq : p ≤ q) : p = q := by
  let : p.asIdeal.FiniteHeight := ⟨Or.inr (hp.2 ▸ ENat.natCast_ne_top c)⟩
  apply PrimeSpectrum.ext
  exact Ideal.eq_of_le_of_height_le p.asIdeal hpq (hq.2.le.trans hp.2.symm.le)

/-- The multiplicative set avoiding every least-height support point. -/
def heightStratumComplement (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (c : ℕ) :
    Submonoid R where
  carrier := {s | ∀ p ∈ heightStratum Z c, s ∉ p.asIdeal}
  one_mem' := fun p _ => p.asIdeal.primeCompl.one_mem
  mul_mem' hs ht := fun p hp => p.asIdeal.primeCompl.mul_mem (hs p hp) (ht p hp)

@[simp]
lemma mem_heightStratumComplement {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {c : ℕ} {s : R} :
    s ∈ heightStratumComplement Z c ↔ ∀ p ∈ heightStratum Z c, s ∉ p.asIdeal := Iff.rfl

/-- Avoiding all height-c support points raises the height bound of the cut. -/
lemma HeightAtLeast.cut_succ {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} {c : ℕ}
    (h : HeightAtLeast Z c) (s : R)
    (hs : ∀ p ∈ heightStratum Z c, s ∉ p.asIdeal) :
    HeightAtLeast (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))) (c + 1) := by
  intro p hp
  have hne : p.asIdeal.height ≠ (c : ℕ∞) := by
    intro he
    exact hs p ⟨hp.1, he⟩ (hp.2 (Ideal.subset_span (Set.mem_singleton s)))
  have ht : (c : ℕ∞) < p.asIdeal.height := lt_of_le_of_ne (h p hp.1) hne.symm
  simpa only [Nat.cast_add, Nat.cast_one] using
    (ENat.add_one_le_iff (ENat.natCast_ne_top c)).mpr ht

lemma HeightAtLeast.cut_succ_of_mem_complement
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} {c : ℕ} (h : HeightAtLeast Z c)
    {s : R} (hs : s ∈ heightStratumComplement Z c) :
    HeightAtLeast (Z ⊓ supportZeroLocus (Ideal.span ({s} : Set R))) (c + 1) :=
  h.cut_succ s hs

lemma HeightAtLeast.succ_of_heightStratum_empty
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} {c : ℕ} (h : HeightAtLeast Z c)
    (he : heightStratum Z c = ∅) : HeightAtLeast Z (c + 1) := by
  intro p hp
  have hne : p.asIdeal.height ≠ (c : ℕ∞) := by
    intro hc
    have hm : p ∈ heightStratum Z c := ⟨hp, hc⟩
    rw [he] at hm
    exact hm
  simpa only [Nat.cast_add, Nat.cast_one] using
    (ENat.add_one_le_iff (ENat.natCast_ne_top c)).mpr (lt_of_le_of_ne (h p hp) hne.symm)

/-- Above a finite ring-dimension bound, a closed support must be empty. -/
lemma HeightAtLeast.eq_bot_of_dimension_bound
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} {d : ℕ}
    (h : HeightAtLeast Z (d + 1)) (hd : ringKrullDim R ≤ d) : Z = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro p hp
  have hb : (p.asIdeal.height : WithBot ℕ∞) ≤ d :=
    p.asIdeal.height_le_ringKrullDim_of_isPrime.trans hd
  have hc : (d + 1 : ℕ∞) ≤ (d : ℕ∞) :=
    (h p hp).trans (WithBot.coe_le_coe.mp hb)
  have hn : d + 1 ≤ d := by exact_mod_cast hc
  omega

end Adams
end SerrePositivity

end SupportHeightPart

section SemilocalSupportPart

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

end SemilocalSupportPart

section ModuleSupportHeightPart

namespace SerrePositivity
open Adams
variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Nonzero module support dimensions are recovered from their natural values. -/
lemma natCast_dimToNat_supportDim (M : Type u) [AddCommGroup M] [Module R M]
    [Nontrivial M] :
    (dimToNat (Module.supportDim R M) : WithBot ℕ∞) = Module.supportDim R M := by
  obtain ⟨p, _, _, hp⟩ := exists_minimumHeight_support_prime (R := R) M
  have := finiteRingKrullDim_primeQuotient p
  rw [hp]
  exact natCast_dimToNat_ringKrullDim (R ⧸ p.asIdeal)

/-- The numerical support codimension and dimension add to the ring dimension. -/
lemma regular_supportCodimension_toNat_add_dimToNat (M : Type u)
    [AddCommGroup M] [Module R M] [Nontrivial M] :
    (supportCodimension R M).toNat + dimToNat (Module.supportDim R M) =
      dimToNat (ringKrullDim R) := by
  obtain ⟨p, _, hc, hd⟩ := exists_minimumHeight_support_prime (R := R) M
  rw [hc, hd]
  exact regular_primeHeight_toNat_add_quotientDimToNat p

/-- The least support height bounds every point of the closed module support. -/
lemma heightAtLeast_finiteModuleClosedSupport (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    HeightAtLeast (finiteModuleClosedSupport R M) (supportCodimension R M).toNat := by
  obtain ⟨q, _, hc, _⟩ := exists_minimumHeight_support_prime (R := R) M
  intro p hp
  have hp' : p ∈ Module.support R M := by
    rw [← finiteModuleClosedSupport_coe R M]
    exact hp
  rw [hc, natCast_primeHeight_toNat q]
  rw [← hc]
  exact supportCodimension_le_height hp'

omit [IsRegularLocalRing R] in
/-- Empty module support admits any height lower bound. -/
lemma heightAtLeast_finiteModuleClosedSupport_of_subsingleton (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Subsingleton M] (c : ℕ) :
    HeightAtLeast (finiteModuleClosedSupport R M) c := by
  intro p hp
  have hp' : p ∈ Module.support R M := by
    rw [← finiteModuleClosedSupport_coe R M]
    exact hp
  simp only [Module.support_eq_empty, Set.mem_empty_iff_false] at hp'

/-- Strict dimension bounds yield support height bounds, including empty supports. -/
lemma exists_supportHeight_sum_gt (M N : Type u)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hdim : Module.supportDim R M + Module.supportDim R N < ringKrullDim R) :
    ∃ cM cN : ℕ, HeightAtLeast (finiteModuleClosedSupport R M) cM ∧
      HeightAtLeast (finiteModuleClosedSupport R N) cN ∧
      dimToNat (ringKrullDim R) < cM + cN := by
  classical
  cases subsingleton_or_nontrivial M with
  | inl hM =>
      let : Subsingleton M := hM
      refine ⟨dimToNat (ringKrullDim R) + 1, 0,
        heightAtLeast_finiteModuleClosedSupport_of_subsingleton M _,
        heightAtLeast_zero _, ?_⟩
      omega
  | inr hM =>
      let : Nontrivial M := hM
      cases subsingleton_or_nontrivial N with
      | inl hN =>
          let : Subsingleton N := hN
          refine ⟨0, dimToNat (ringKrullDim R) + 1, heightAtLeast_zero _,
            heightAtLeast_finiteModuleClosedSupport_of_subsingleton N _, ?_⟩
          omega
      | inr hN =>
          let : Nontrivial N := hN
          refine ⟨(supportCodimension R M).toNat, (supportCodimension R N).toNat,
            heightAtLeast_finiteModuleClosedSupport M,
            heightAtLeast_finiteModuleClosedSupport N, ?_⟩
          have hM' := regular_supportCodimension_toNat_add_dimToNat (R := R) M
          have hN' := regular_supportCodimension_toNat_add_dimToNat (R := R) N
          rw [← natCast_dimToNat_supportDim M, ← natCast_dimToNat_supportDim N,
            ← natCast_dimToNat_ringKrullDim R] at hdim
          have hd : dimToNat (Module.supportDim R M) + dimToNat (Module.supportDim R N) <
              dimToNat (ringKrullDim R) := by exact_mod_cast hdim
          omega

end SerrePositivity

end ModuleSupportHeightPart
