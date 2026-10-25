module

public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionWittNormalizedIdeal

/-! # 実際の有限δ剰余商と正規化モニック商の同型 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 実際の有限δ剰余商を、具体的モニック関係式の商へ移す環同型。 -/
def deltaDivisionFiniteNormalizedQuotientEquiv (D : DeltaStructure p A)
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) (N : ℕ) :
    (RelativeFreeDeltaRing (R := A) σ ⧸
      (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        deltaDivisionFiniteRelationIdeal D d a (N + 1))) ≃+*
      (RelativeFreeDeltaRing (R := A) σ ⧸
        (deltaDivisionFirstResidueIdeal D d a ⊔
          deltaDivisionFiniteNormalizedWittIdeal D d a u N)) :=
  Ideal.quotientEquiv _ _ (relativeFreeWittCoordinateEquiv D hpA).symm.toRingEquiv
    (deltaDivisionFiniteRelationIdeal_inverse_map_eq_first_sup_normalized
      D hpA hpL hg d a u hu N).symm

/-- 正規化商同型と、実際の源環の標準商射の図式。 -/
theorem deltaDivisionFiniteNormalizedQuotientEquiv_mk (D : DeltaStructure p A)
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) (N : ℕ)
    (f : RelativeFreeDeltaRing (R := A) σ) :
    deltaDivisionFiniteNormalizedQuotientEquiv D hpA hpL hg d a u hu N
      (Ideal.Quotient.mk _ f) =
        Ideal.Quotient.mk _ (relativeFreeWittInverseMap D hpA f) := by
  rfl

/-- 正規化商同型は基底係数の標準像を固定する。 -/
theorem deltaDivisionFiniteNormalizedQuotientEquiv_C (D : DeltaStructure p A)
    (hpA : Function.Injective (fun a : A => (p : A) * a))
    (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) (N : ℕ) (b : A) :
    deltaDivisionFiniteNormalizedQuotientEquiv D hpA hpL hg d a u hu N
      (Ideal.Quotient.mk _ (MvPolynomial.C b)) =
        Ideal.Quotient.mk _ (MvPolynomial.C b) := by
  rw [deltaDivisionFiniteNormalizedQuotientEquiv_mk]
  exact congrArg (Ideal.Quotient.mk _) (AlgHom.commutes (relativeFreeWittInverseMap D hpA) b)

end SerrePositivity.BhattScholze
