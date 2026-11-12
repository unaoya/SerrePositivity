module

public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitMap
public import SerrePositivity.CommutativeAlgebra.UniversalHomeomorphism.Basic

/-!
概要：Frobenius 順極限の nil 不変性と普遍同相に関する不変性。
方針：nil な核と p 冪の像の判定を、実際の商写像・普遍同相へ適用する。
規約：零環を除外せず、導来関手の H の主張は行わない。
使われ方：BST13 Lemma 3.5 の affine の環の計算、後の Čech 比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
variable (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) (hB : (p : B) = 0)

include hA in
/-- p が零であることは、零環になる商にも保たれる。 -/
theorem frobeniusQuotientPrimeCast (J : Ideal A) : (p : A ⧸ J) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk J), hA, map_zero]

/-- nil イデアルによる商の実際の射は Frobenius 順極限上で全単射。 -/
theorem frobeniusDirectLimitQuotient_bijective (J : Ideal A) (hJ : J ≤ nilradical A) :
    Function.Bijective (frobeniusDirectLimitMap p hp hA
      (frobeniusQuotientPrimeCast p hA J) (Ideal.Quotient.mk J)) := by
  constructor
  · apply frobeniusDirectLimitMap_injective
    intro a ha
    exact mem_nilradical.mp (hJ (Ideal.Quotient.eq_zero_iff_mem.mp ha))
  · apply frobeniusDirectLimitMap_surjective
    intro b
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨0, a, by simpa using ha⟩

/-- nil イデアルによる商と元の環の Frobenius 順極限の canonical な環同型。 -/
def frobeniusDirectLimitQuotientEquiv (J : Ideal A) (hJ : J ≤ nilradical A) :
    FrobeniusDirectLimit A p hp hA ≃+*
      FrobeniusDirectLimit (A ⧸ J) p hp (frobeniusQuotientPrimeCast p hA J) :=
  RingEquiv.ofBijective _ (frobeniusDirectLimitQuotient_bijective p hp hA J hJ)

/-- 普遍同相な環準同型は Frobenius 順極限上で全単射。 -/
theorem frobeniusDirectLimitUniversalHomeomorphism_bijective (f : A →+* B)
    (hf : SerrePositivity.CommutativeAlgebra.IsUniversalHomeomorphism f) :
    Function.Bijective (frobeniusDirectLimitMap p hp hA hB f) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hk, hs⟩ :=
    (SerrePositivity.CommutativeAlgebra.isUniversalHomeomorphism_iff_charP p hA f).mp hf
  constructor
  · apply frobeniusDirectLimitMap_injective
    intro a ha
    exact mem_nilradical.mp (hk ha)
  · apply frobeniusDirectLimitMap_surjective
    intro b
    obtain ⟨e, a, ha⟩ := hs b
    exact ⟨e, a, ha⟩

/-- 普遍同相が誘導する Frobenius 順極限の canonical な環同型。 -/
def frobeniusDirectLimitUniversalHomeomorphismEquiv (f : A →+* B)
    (hf : SerrePositivity.CommutativeAlgebra.IsUniversalHomeomorphism f) :
    FrobeniusDirectLimit A p hp hA ≃+* FrobeniusDirectLimit B p hp hB :=
  RingEquiv.ofBijective _
    (frobeniusDirectLimitUniversalHomeomorphism_bijective p hp hA hB f hf)

end SerrePositivity.AlgebraicGeometry
