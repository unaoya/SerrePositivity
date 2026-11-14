module

public import SerrePositivity.AlgebraicGeometry.MinimalPrimeFiniteRelations
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
概要：極小素点の近くで、係数環の整域商から実際の局所化への射を作る。
方針：縮約した素イデアルの有限個の生成元を同時に消して商の普遍性を使う。
規約：有限生成性は縮約イデアルに要求する。Noether な係数環では自動的に満たされる。
使われ方：非 Noether 基底の極小素点の近くで、一般平坦性を整域の模型から戻す係数移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v

/-- 極小素点の近傍で、係数の縮約した素イデアルによる商を経由する射を構成する。 -/
theorem exists_away_quotient_factor_of_minimalPrime
    {R : Type u} [CommRing R] [IsReduced R] {S : Type v} [CommRing S]
    (f : S →+* R) {p : Ideal R} (hp : p ∈ minimalPrimes R)
    (hfg : (p.comap f).FG) :
    ∃ (s : R) (_ : s ∉ p) (l : S ⧸ p.comap f →+* Localization.Away s),
      l.comp (Ideal.Quotient.mk (p.comap f)) = (algebraMap R (Localization.Away s)).comp f := by
  obtain ⟨s, hs, hkill⟩ := exists_common_annihilator_fg_minimalPrime hp (hfg.map f)
    (Ideal.map_le_iff_le_comap.mpr le_rfl)
  have hz (a : S) (ha : a ∈ p.comap f) :
      ((algebraMap R (Localization.Away s)).comp f) a = 0 := by
    apply (IsLocalization.map_eq_zero_iff (Submonoid.powers s) (Localization.Away s) (f a)).mpr
    exact ⟨⟨s, ⟨1, pow_one s⟩⟩, hkill (f a) (Ideal.mem_map_of_mem f ha)⟩
  refine ⟨s, hs, Ideal.Quotient.lift (p.comap f)
    ((algebraMap R (Localization.Away s)).comp f) hz, ?_⟩
  ext a
  rfl

end SerrePositivity.AlgebraicGeometry
