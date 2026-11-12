module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
概要：Spec 上全射な環の射に沿う、拡大イデアルの根基の逆像。
方針：中心を含む各素イデアルを持ち上げ、根基を素イデアルの交叉として計算する。
規約：整性や単射性は不要。
使われ方：有限射の導手の四角形を、指定した中心の四角形に移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable (f : A →+* B) (hs : Function.Surjective (PrimeSpectrum.comap f))

include hs in
/-- Spec 上全射なら、拡大イデアルの根基の逆像は元のイデアルの根基。 -/
theorem surjectiveSpectrum_comap_radical_map (I : Ideal A) :
    ((I.map f).radical).comap f = I.radical := by
  apply le_antisymm
  · rw [Ideal.radical_eq_sInf I]
    apply le_sInf
    intro P hP
    obtain ⟨Q, hQ⟩ := hs ⟨P, hP.2⟩
    have hQP : Q.asIdeal.comap f = P := congrArg PrimeSpectrum.asIdeal hQ
    have hm : I.map f ≤ Q.asIdeal := Ideal.map_le_iff_le_comap.mpr (by rw [hQP]; exact hP.1)
    intro a ha
    have hqa : f a ∈ Q.asIdeal := Q.isPrime.radical_le_iff.mpr hm ha
    rw [← hQP]
    exact hqa
  · rw [Ideal.comap_radical]
    exact Ideal.radical_mono Ideal.le_comap_map

include hs in
/-- Spec 上全射なら、拡大して戻したイデアルの根基は変わらない。 -/
theorem surjectiveSpectrum_radical_comap_map (I : Ideal A) :
    ((I.map f).comap f).radical = I.radical := by
  rw [← Ideal.comap_radical]
  exact surjectiveSpectrum_comap_radical_map f hs I

end SerrePositivity.AlgebraicGeometry
