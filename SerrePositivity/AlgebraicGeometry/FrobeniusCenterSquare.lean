module

public import SerrePositivity.AlgebraicGeometry.FrobeniusPowerCenter
public import SerrePositivity.AlgebraicGeometry.FrobeniusConductorSquare
public import SerrePositivity.AlgebraicGeometry.SquareLiftTransport

/-!
概要：導手に入る中心の冪から、指定した中心の Frobenius 四角形を得る。
方針：冪の商を共通対象とし、実際の因子写像で持ち上げを移送する。
規約：Spec 全射性と導手への包含を明示的な仮定にする。
使われ方：有限変更の四角形の真ん中の完全性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

/-- 中心の正の冪の拡大が像に入れば、指定した中心の Frobenius 四角形で同時に持ち上がる。 -/
theorem frobeniusCenterSquare_lift
    (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) (hB : (p : B) = 0)
    (f : A →+* B) (hs : Function.Surjective (PrimeSpectrum.comap f))
    (I : Ideal A) (n : ℕ) (hn : n ≠ 0)
    (hK : ∀ b ∈ (I ^ n).map f, ∃ a : A, f a = b)
    (x : FrobeniusDirectLimit B p hp hB)
    (y : FrobeniusDirectLimit (A ⧸ I) p hp (frobeniusQuotientPrimeCast p hA I))
    (he : frobeniusDirectLimitMap p hp hB (frobeniusQuotientPrimeCast p hB (I.map f))
        (Ideal.Quotient.mk (I.map f)) x =
      frobeniusDirectLimitMap p hp (frobeniusQuotientPrimeCast p hA I)
        (frobeniusQuotientPrimeCast p hB (I.map f))
        (Ideal.quotientMap (I.map f) f Ideal.le_comap_map) y) :
    ∃ a : FrobeniusDirectLimit A p hp hA,
      frobeniusDirectLimitMap p hp hA hB f a = x ∧
      frobeniusDirectLimitMap p hp hA (frobeniusQuotientPrimeCast p hA I)
        (Ideal.Quotient.mk I) a = y := by
  let K := (I ^ n).map f
  let L := K.comap f
  have hKI : K ≤ I.map f := Ideal.map_mono (Ideal.pow_le_self hn)
  let g₀ := frobeniusDirectLimitMap p hp hA (frobeniusQuotientPrimeCast p hA (I ^ n))
    (Ideal.Quotient.mk (I ^ n))
  let g₁ := frobeniusDirectLimitMap p hp hA (frobeniusQuotientPrimeCast p hA L)
    (Ideal.Quotient.mk L)
  let g₂ := frobeniusDirectLimitMap p hp hA (frobeniusQuotientPrimeCast p hA I)
    (Ideal.Quotient.mk I)
  let h₁ := frobeniusDirectLimitMap p hp hB (frobeniusQuotientPrimeCast p hB K)
    (Ideal.Quotient.mk K)
  let h₂ := frobeniusDirectLimitMap p hp hB (frobeniusQuotientPrimeCast p hB (I.map f))
    (Ideal.Quotient.mk (I.map f))
  let k₁ := frobeniusDirectLimitMap p hp (frobeniusQuotientPrimeCast p hA L)
    (frobeniusQuotientPrimeCast p hB K) (Ideal.quotientMap K f le_rfl)
  let k₂ := frobeniusDirectLimitMap p hp (frobeniusQuotientPrimeCast p hA I)
    (frobeniusQuotientPrimeCast p hB (I.map f))
    (Ideal.quotientMap (I.map f) f Ideal.le_comap_map)
  let u := frobeniusDirectLimitMap p hp (frobeniusQuotientPrimeCast p hA (I ^ n))
    (frobeniusQuotientPrimeCast p hA L) (Ideal.Quotient.factor Ideal.le_comap_map)
  let v := frobeniusDirectLimitMap p hp (frobeniusQuotientPrimeCast p hA (I ^ n))
    (frobeniusQuotientPrimeCast p hA I) (Ideal.Quotient.factor (Ideal.pow_le_self hn))
  let w := frobeniusDirectLimitMap p hp (frobeniusQuotientPrimeCast p hB K)
    (frobeniusQuotientPrimeCast p hB (I.map f)) (Ideal.Quotient.factor hKI)
  have hw : Function.Injective w := by
    apply (frobeniusQuotientFactor_bijective p hp hB hKI ?_).injective
    change I.map f ≤ ((I ^ n).map f).radical
    rw [Ideal.map_pow, Ideal.radical_pow _ hn]
    exact Ideal.le_radical
  apply squareLift_transport (frobeniusDirectLimitMap p hp hA hB f)
    g₀ g₁ g₂ h₁ h₂ k₁ k₂ u v w
    (frobeniusContractedPowerCenter_bijective p hp hA f hs I n).injective
    (frobeniusPowerCenter_bijective p hp hA I n hn).surjective hw
    ?_ ?_ ?_ ?_ (frobeniusConductorSquare_lift p hp hA hB f K hK) x y he
  · intro a
    obtain ⟨m, a, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap A p hp hA) a
    rfl
  · intro a
    obtain ⟨m, a, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap A p hp hA) a
    rfl
  · intro b
    obtain ⟨m, b, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap B p hp hB) b
    rfl
  · intro c
    obtain ⟨m, c, rfl⟩ := DirectLimit.exists_eq_mk
      (frobeniusDirectSystemMap (A ⧸ I ^ n) p hp (frobeniusQuotientPrimeCast p hA (I ^ n))) c
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    rfl

end SerrePositivity.AlgebraicGeometry
