module

public import SerrePositivity.AlgebraicGeometry.FrobeniusCenterSquare
public import SerrePositivity.AlgebraicGeometry.LocalizedCokernelSupport
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
概要：有限環拡大の局所全射性を、指定中心の Frobenius 四角形へ接続する。
方針：余核の台から導手の正の冪を選び、中心比較に渡す。
規約：中心外の仮定は実際の局所化した線形写像の全射性。
使われ方：有限変更に対する短完全性の環論部分。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

/-- Spec 上全射な射は、Frobenius 順極限で単射になる。 -/
theorem frobeniusDirectLimitMap_injective_of_surjectiveSpectrum
    (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) (hB : (p : B) = 0)
    (f : A →+* B) (hs : Function.Surjective (PrimeSpectrum.comap f)) :
    Function.Injective (frobeniusDirectLimitMap p hp hA hB f) := by
  apply frobeniusDirectLimitMap_injective p hp hA hB f
  have hk : RingHom.ker f ≤ nilradical A :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).mp hs.denseRange
  intro a ha
  exact hk ha

/-- 有限環拡大で中心外が局所全射なら、指定中心の四角形で同時に持ち上がる。 -/
theorem frobeniusFiniteModificationSquare_lift
    [Algebra A B] [Module.Finite A B]
    (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) (hB : (p : B) = 0)
    (hs : Function.Surjective (PrimeSpectrum.comap (algebraMap A B)))
    (I : Ideal A) (hI : I.FG)
    (hloc : ∀ P : PrimeSpectrum A, P ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      Function.Surjective (LocalizedModule.map P.asIdeal.primeCompl (Algebra.linearMap A B)))
    (x : FrobeniusDirectLimit B p hp hB)
    (y : FrobeniusDirectLimit (A ⧸ I) p hp (frobeniusQuotientPrimeCast p hA I))
    (he : frobeniusDirectLimitMap p hp hB
        (frobeniusQuotientPrimeCast p hB (I.map (algebraMap A B)))
        (Ideal.Quotient.mk (I.map (algebraMap A B))) x =
      frobeniusDirectLimitMap p hp (frobeniusQuotientPrimeCast p hA I)
        (frobeniusQuotientPrimeCast p hB (I.map (algebraMap A B)))
        (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B) Ideal.le_comap_map) y) :
    ∃ a : FrobeniusDirectLimit A p hp hA,
      frobeniusDirectLimitMap p hp hA hB (algebraMap A B) a = x ∧
      frobeniusDirectLimitMap p hp hA (frobeniusQuotientPrimeCast p hA I)
        (Ideal.Quotient.mk I) a = y := by
  obtain ⟨n, hn⟩ := finiteLocalizedSurjective_exists_pow_map_lift I hI hloc
  apply frobeniusCenterSquare_lift p hp hA hB (algebraMap A B) hs I (n + 1)
    (Nat.succ_ne_zero n) ?_ x y he
  intro b hb
  exact hn b (Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) hb)

end SerrePositivity.AlgebraicGeometry
