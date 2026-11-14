module

public import SerrePositivity.AlgebraicGeometry.MinimalPrimeQuotientFactor

/-!
概要：極小素点での係数の整域商の基本開を、元の基底の基本開へ戻す。
方針：関係を消す元と、商の非零元の代表の像の積を反転する。
規約：返す射は係数環からの二つの構造写像と可換。非零元が極小素点を避けることを保持する。
使われ方：整域上の一般自由性の基本開の、非 Noether 基底への底変換。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v

/-- 整域商の非零元を反転する射は、元の基底の極小素点の基本開へ移せる。 -/
theorem exists_away_quotient_localization_factor_of_minimalPrime
    {R : Type u} [CommRing R] [IsReduced R] {S : Type v} [CommRing S]
    (f : S →+* R) {p : Ideal R} (hp : p ∈ minimalPrimes R)
    (hfg : (p.comap f).FG) (t : S ⧸ p.comap f) (ht : t ≠ 0) :
    ∃ (r : R) (_ : r ∉ p)
      (l : Localization.Away t →+* Localization.Away r),
      (l.comp (algebraMap (S ⧸ p.comap f) (Localization.Away t))).comp
          (Ideal.Quotient.mk (p.comap f)) = (algebraMap R (Localization.Away r)).comp f := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
  obtain ⟨s, hs, l, hl⟩ := exists_away_quotient_factor_of_minimalPrime f hp hfg
  have ha : f a ∉ p := by
    intro h
    exact ht (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  let r := s * f a
  let D := Localization.Away r
  let m : Localization.Away s →+* D :=
    IsLocalization.Away.awayToAwayRight s (f a)
  let q : S ⧸ p.comap f →+* D := m.comp l
  have hq : q.comp (Ideal.Quotient.mk (p.comap f)) = (algebraMap R D).comp f := by
    ext b
    change m (l (Ideal.Quotient.mk (p.comap f) b)) = algebraMap R D (f b)
    have hlb : l (Ideal.Quotient.mk (p.comap f) b) =
        algebraMap R (Localization.Away s) (f b) := RingHom.congr_fun hl b
    rw [hlb]
    exact IsLocalization.Away.awayToAwayRight_eq s (f a) (f b)
  have hu : IsUnit (q (Ideal.Quotient.mk (p.comap f) a)) := by
    have hqa : q (Ideal.Quotient.mk (p.comap f) a) = algebraMap R D (f a) :=
      RingHom.congr_fun hq a
    rw [hqa]
    exact IsLocalization.Away.isUnit_of_dvd (S := D) r ⟨s, mul_comm _ _⟩
  let l' : Localization.Away (Ideal.Quotient.mk (p.comap f) a) →+* D :=
    IsLocalization.Away.lift _ hu
  refine ⟨r, fun h ↦ (hp.1.1.mem_or_mem h).elim hs ha, l', ?_⟩
  rw [show l'.comp (algebraMap _ _) = q from IsLocalization.Away.lift_comp _ hu]
  exact hq

end SerrePositivity.AlgebraicGeometry
