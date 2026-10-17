module

public import SerrePositivity.CommutativeAlgebra.GenericEtale
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Smooth.Flat

/-! # Prop 2.4.7：D(g) の rank による有限開閉分解

元の局所化代数の stalk rank を、実際の D(g) へ移す。
閉包の環やその perfectoid 化との比較はここでは主張しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST

/-- 元の局所化写像による Spec R[1/g] と D(g) の同相。 -/
def prop247_awaySpectrumHomeomorph (R : Type u) [CommRing R] (g : R) :
    PrimeSpectrum (Localization.Away g) ≃ₜ (PrimeSpectrum.basicOpen g) :=
  (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away g) g).isEmbedding.toHomeomorph
    |>.trans (Homeomorph.setCongr
      (PrimeSpectrum.localization_away_comap_range (Localization.Away g) g))

/-- 同相の点への作用は元の局所化環写像の comap そのものである。 -/
@[simp] theorem prop247_awaySpectrumHomeomorph_apply
    (R : Type u) [CommRing R] (g : R) (x : PrimeSpectrum (Localization.Away g)) :
    ((prop247_awaySpectrumHomeomorph R g x) : PrimeSpectrum R) =
      PrimeSpectrum.comap (algebraMap R (Localization.Away g)) x := rfl

/-- D(g) 上の rank は、元の S[1/g] の局所加群の rank である。 -/
def prop247_awayRank (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (g : R) : (PrimeSpectrum.basicOpen g) → ℕ := by
  letI := GenericEtale.awayAlgebra R S g
  exact fun x => Module.rankAtStalk (R := Localization.Away g)
    (Localization.Away (algebraMap R S g)) ((prop247_awaySpectrumHomeomorph R g).symm x)

/-- 元の局所化の各点で、D(g) に移した rank は元の stalk rank に一致する。 -/
@[simp] theorem prop247_awayRank_at_localization
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (g : R) (x : PrimeSpectrum (Localization.Away g)) :
    letI := GenericEtale.awayAlgebra R S g
    prop247_awayRank R S g (prop247_awaySpectrumHomeomorph R g x) =
      Module.rankAtStalk (R := Localization.Away g)
        (Localization.Away (algebraMap R S g)) x := by
  letI := GenericEtale.awayAlgebra R S g
  simp only [prop247_awayRank, Homeomorph.symm_apply_apply]

/-- 有限 étale な実局所化代数の rank は D(g) 上で局所定数である。 -/
theorem prop247_awayRank_isLocallyConstant
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] (g : R) :
    letI := GenericEtale.awayAlgebra R S g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)) →
      IsLocallyConstant (prop247_awayRank R S g) := by
  letI := GenericEtale.awayAlgebra R S g
  intro hetale
  letI := hetale
  letI := GenericEtale.finite_away R S g
  letI := Module.FinitePresentation.of_finite_of_finitePresentation
    (Localization.Away g) (Localization.Away (algebraMap R S g))
  exact (Module.isLocallyConstant_rankAtStalk
    (R := Localization.Away g) (M := Localization.Away (algebraMap R S g))).comp_continuous
      (prop247_awaySpectrumHomeomorph R g).symm.continuous

/-- 原典の rank 別開閉部分は有限個で D(g) を被覆し、互いに素である。
rank 0 および D(g) が空の場合を含む。 -/
theorem prop247_awayRank_finite_clopen_decomposition
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] (g : R) :
    letI := GenericEtale.awayAlgebra R S g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)) →
      ∃ t : Finset ℕ,
        (∀ n, n ∈ t ↔ ∃ x, prop247_awayRank R S g x = n) ∧
        (∀ n, IsClopen {x | prop247_awayRank R S g x = n}) ∧
        (∀ x, prop247_awayRank R S g x ∈ t) ∧
        (∀ n m : ℕ, n ≠ m → Disjoint
          {x | prop247_awayRank R S g x = n} {x | prop247_awayRank R S g x = m}) := by
  letI := GenericEtale.awayAlgebra R S g
  intro hetale
  classical
  letI : CompactSpace (PrimeSpectrum.basicOpen g) :=
    isCompact_iff_compactSpace.mp (PrimeSpectrum.isCompact_basicOpen g)
  have h := prop247_awayRank_isLocallyConstant R S g hetale
  let t := h.range_finite.toFinset
  refine ⟨t, ?_, h.isClopen_fiber, ?_, ?_⟩
  · intro n
    exact Set.Finite.mem_toFinset _
  · intro x
    exact h.range_finite.mem_toFinset.mpr ⟨x, rfl⟩
  · intro n m hnm
    apply Set.disjoint_left.mpr
    intro x hn hm
    exact hnm (hn.symm.trans hm)

end SerrePositivity.CLMST
