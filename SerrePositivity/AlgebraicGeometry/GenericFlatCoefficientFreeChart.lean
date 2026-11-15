module

public import SerrePositivity.AlgebraicGeometry.GenericFlatNoetherianCoefficients
public import SerrePositivity.AlgebraicGeometry.GenericFreeAlgebra
public import Mathlib.RingTheory.FiniteStability

/-!
概要：極小素点の一般自由開を、有限生成の係数部分代数上でも実現する。
方針：商の有限関係を部分代数上で消し、整域商の一般自由性を底変換する。
規約：元の被約基底の Noether 性は仮定しない。
使われ方：一般点集合が準コンパクトな基底の、平坦開を伴う Noether 模型。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
universe u

/-- 一般自由開への係数移送は、有限生成の係数部分代数で実現できる。 -/
theorem exists_fg_subalgebra_free_basicOpen_at_minimalPrime
    (A R S : Type u) [CommRing A] [IsNoetherianRing A]
    [CommRing R] [IsReduced R] [Algebra A R]
    [CommRing S] [Algebra A S] [Algebra.FiniteType A S]
    {p : Ideal R} (hp : p ∈ minimalPrimes R) :
    ∃ T : Subalgebra A R, T.FG ∧ ∃ t : T, (t : R) ∉ p ∧
      Module.Free (Localization.Away t) (Localization.Away t ⊗[A] S) := by
  let f := algebraMap A R
  let J := p.comap f
  have : p.IsPrime := hp.1.1
  have : J.IsPrime := Ideal.IsPrime.comap f
  let Q := A ⧸ J
  let C := Q ⊗[A] S
  obtain ⟨t, ht, hfree⟩ := exists_nonzero_free_localization_of_finiteType Q C
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
  obtain ⟨T, hT, s, hs, l, hl⟩ :=
    exists_fg_subalgebra_quotient_localization_factor hp J.fg_of_isNoetherianRing
  have ha : f a ∉ p := by
    intro h
    exact ht (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  let r := s * algebraMap A T a
  let D := Localization.Away r
  let m : Localization.Away s →+* D :=
    IsLocalization.Away.awayToAwayRight s (algebraMap A T a)
  let q : Q →+* D := m.comp l
  have hq : q.comp (Ideal.Quotient.mk J) = (algebraMap T D).comp (algebraMap A T) := by
    ext b
    change m (l (Ideal.Quotient.mk J b)) = algebraMap T D (algebraMap A T b)
    rw [show l (Ideal.Quotient.mk J b) = algebraMap T (Localization.Away s) (algebraMap A T b)
      from RingHom.congr_fun hl b]
    exact IsLocalization.Away.awayToAwayRight_eq s (algebraMap A T a) (algebraMap A T b)
  have hu : IsUnit (q (Ideal.Quotient.mk J a)) := by
    rw [show q (Ideal.Quotient.mk J a) = algebraMap T D (algebraMap A T a)
      from RingHom.congr_fun hq a]
    exact IsLocalization.Away.isUnit_of_dvd (S := D) r ⟨s, mul_comm _ _⟩
  let L := Localization.Away (Ideal.Quotient.mk J a)
  let l' : L →+* D := IsLocalization.Away.lift _ hu
  have hl' : (l'.comp (algebraMap Q L)).comp (Ideal.Quotient.mk J) =
      (algebraMap T D).comp (algebraMap A T) := by
    rw [show l'.comp (algebraMap Q L) = q from IsLocalization.Away.lift_comp _ hu]
    exact hq
  let : Algebra A D := inferInstance
  let : Algebra A L := inferInstance
  let : Algebra L D := l'.toAlgebra
  let : Algebra Q D := (l'.comp (algebraMap Q L)).toAlgebra
  have : IsScalarTower A Q L := inferInstance
  have : IsScalarTower Q L D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A L D := IsScalarTower.of_algebraMap_eq fun b ↦
    (RingHom.congr_fun hl' b).symm
  have : IsScalarTower A Q D := IsScalarTower.of_algebraMap_eq fun b ↦
    (RingHom.congr_fun hl' b).symm
  let : Module.Free L (L ⊗[Q] C) := hfree
  let : Module.Free D (D ⊗[L] (L ⊗[Q] C)) := inferInstance
  let : Module.Free D (D ⊗[Q] C) := Module.Free.of_equiv
    (Algebra.TensorProduct.cancelBaseChange Q L D D C).toLinearEquiv
  let : Module.Free D (D ⊗[A] S) := Module.Free.of_equiv
    (Algebra.TensorProduct.cancelBaseChange A Q D D S).toLinearEquiv
  refine ⟨T, hT, r, ?_, inferInstance⟩
  change (s : R) * f a ∉ p
  exact fun h ↦ (hp.1.1.mem_or_mem h).elim hs ha

end SerrePositivity.AlgebraicGeometry
