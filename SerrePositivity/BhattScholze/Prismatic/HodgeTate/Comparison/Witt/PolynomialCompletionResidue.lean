module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.BigPDModel
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePrincipalResidue
public import Mathlib.RingTheory.Polynomial.Basic
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineReductionPushout
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 完備多項式の p を法とする剰余

## 概要
p 正則な係数環では、完備多項式を p で割ると剰余係数上の通常の多項式環になる。

## 方針
主完備化の単位の mod p での同型と、多項式の係数写像の核の計算をつなぐ。

## 規約
同型は多項式の変数を完備化単位の剰余へ送る。

## 使われ方
BS 著者版 Theorem 6.4 の大きい枠と有限枠の剰余環の照合。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

local notation "C" => (A ⧸ P.ideal)

variable (hp : Function.Injective (fun x : A ⧸ P.ideal => (p : A ⧸ P.ideal) * x))
variable (Q : Poly (A ⧸ P.ideal))

local notation "B" => MvPolynomial (Fin Q.n) C
local notation "I" => Ideal.span {(p : C)}
local notation "L" => Ideal.span {(p : B)}

/-- 係数の剰余を取る写像の核は多項式環の p の生成するイデアル。 -/
private theorem ker_polyMap_modPrime :
    RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk I) :
      B →+* MvPolynomial (Fin Q.n) (C ⧸ I)) = L := by
  rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_span, Set.image_singleton,
    map_natCast]

private def polyQuotientModPrimeEquiv : B ⧸ L ≃+* MvPolynomial (Fin Q.n) (C ⧸ I) :=
  (Ideal.quotEquivOfEq (ker_polyMap_modPrime P Q).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (MvPolynomial.map_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective))

private theorem polyQuotientModPrimeEquiv_mk (x : B) :
    polyQuotientModPrimeEquiv P Q (Ideal.Quotient.mk _ x) =
      MvPolynomial.map (Ideal.Quotient.mk I) x := by
  rw [polyQuotientModPrimeEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact rfl

private def polyCompletionModPrimeMap : B ⧸ L →+* bigResidue P Q :=
  Ideal.quotientMap _ (prismPolynomialUnit P (Fin Q.n)) (by
    rw [Ideal.span_singleton_le_iff_mem]
    change prismPolynomialUnit P (Fin Q.n) (p : B) ∈ Ideal.span {(p : polyCompletion P Q.n)}
    rw [map_natCast]
    exact Ideal.subset_span (Set.mem_singleton _))

include hp in
private theorem polyCompletionModPrimeMap_bijective :
    Function.Bijective (polyCompletionModPrimeMap P Q) := by
  have hB : IsSMulRegular B (p : B) := by
    simpa only [map_natCast] using (show IsSMulRegular C (p : C) from hp).of_flat (S := B)
  let T := CommRingCat.of B
  let f := crystallineModPrimeRingMap p (principalCompletionRingCatUnit p T)
  have : IsIso f := crystallinePrincipalCompletionUnit_isIso_modPrime p T hB
  let e (R : Type u) [CommRing R] :
      (R ⧸ Ideal.span {(p : R)}) ≃+* (R ⧸ Ideal.span {(p : R)^1}) :=
    Ideal.quotEquivOfEq (by rw [pow_one])
  have h : (polyCompletionModPrimeMap P Q : B ⧸ L → bigResidue P Q) =
      (e (polyCompletion P Q.n)).symm ∘ f ∘ e B := by
    funext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change (polyCompletionModPrimeMap P Q) (Ideal.Quotient.mk _ x) =
      (e (polyCompletion P Q.n)).symm (f (e B (Ideal.Quotient.mk _ x)))
    rw [show e B (Ideal.Quotient.mk L x) = Ideal.Quotient.mk _ x from rfl]
    rfl
  rw [h]
  exact (e _).symm.bijective.comp ((ConcreteCategory.bijective_of_isIso f).comp (e B).bijective)

/-- p を法とする完備多項式環の同定。 -/
def polynomialResidueEquiv : MvPolynomial (Fin Q.n) (C ⧸ I) ≃+* bigResidue P Q :=
  (polyQuotientModPrimeEquiv P Q).symm.trans
    (RingEquiv.ofBijective _ (polyCompletionModPrimeMap_bijective P hp Q))

/-- 剰余の同定は未完備多項式の単位と可換。 -/
theorem polynomialResidueEquiv_map (x : B) :
    polynomialResidueEquiv P hp Q (MvPolynomial.map (Ideal.Quotient.mk I) x) =
      Ideal.Quotient.mk _ (prismPolynomialUnit P (Fin Q.n) x) := by
  unfold polynomialResidueEquiv
  rw [RingEquiv.trans_apply, ← polyQuotientModPrimeEquiv_mk P Q,
    RingEquiv.symm_apply_apply]
  rfl

end SerrePositivity.BhattScholze.Prismatic
