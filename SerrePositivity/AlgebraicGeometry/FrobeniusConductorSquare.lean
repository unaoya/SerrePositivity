module

public import SerrePositivity.AlgebraicGeometry.FrobeniusSquareLift
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitInvariance
public import SerrePositivity.AlgebraicGeometry.ConductorSquareLift

/-!
概要：導手に含まれるイデアルによる商の四角形を Frobenius 順極限へ移す。
方針：具体的な商写像を一般の持ち上げ補題へ代入する。
規約：導手の冪の評価は別に供給する入力。
使われ方：BST13 Lemma 3.8 の有限射の四角形。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
variable (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) (hB : (p : B) = 0)
variable (f : A →+* B) (K : Ideal B)
local notation "hQ" => frobeniusQuotientPrimeCast p hB K
local notation "hP" => frobeniusQuotientPrimeCast p hA (K.comap f)

/-- 導手の商の四角形で一致する順極限の元は、元の環の順極限から同時に持ち上がる。 -/
theorem frobeniusConductorSquare_lift
    (hK : ∀ b ∈ K, ∃ a : A, f a = b)
    (x : FrobeniusDirectLimit B p hp hB)
    (y : FrobeniusDirectLimit (A ⧸ K.comap f) p hp hP)
    (he : frobeniusDirectLimitMap p hp hB hQ (Ideal.Quotient.mk K) x =
      frobeniusDirectLimitMap p hp hP hQ (Ideal.quotientMap K f le_rfl) y) :
    ∃ a : FrobeniusDirectLimit A p hp hA,
      frobeniusDirectLimitMap p hp hA hB f a = x ∧
      frobeniusDirectLimitMap p hp hA hP (Ideal.Quotient.mk (K.comap f)) a = y := by
  apply frobeniusSquare_lift p hp hA hB hP hQ f
    (Ideal.Quotient.mk (K.comap f)) (Ideal.Quotient.mk K)
    (Ideal.quotientMap K f le_rfl) ?_ x y he
  intro b c hc
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  exact conductorSquare_lift f K hK a b hc

/-- 導手の四角形の右側の商写像は、Frobenius 順極限でも全射。 -/
theorem frobeniusConductorSquare_quotient_surjective :
    Function.Surjective
      (frobeniusDirectLimitMap p hp hB hQ (Ideal.Quotient.mk K)) := by
  apply frobeniusDirectLimitMap_surjective
  intro b
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨0, a, by simpa using ha⟩

end SerrePositivity.AlgebraicGeometry
