module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaDivisionNormalizedDirectLimitKernel

/-! # 実際の全δ剰余イデアルのWitt正規化と全段環の比較 -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- (p,Cd)を加えた実際のδ閉包は、深さN+1有限剰余イデアルの上限。 -/
theorem deltaDivision_mod_pd_deltaClosure_eq_iSup_finite (D : DeltaStructure p A)
    (d : A) (a : σ → A) :
    Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
      (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a) =
      ⨆ N : ℕ, Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        deltaDivisionFiniteRelationIdeal D d a (N + 1) := by
  let P : Ideal (RelativeFreeDeltaRing (R := A) σ) :=
    Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d}
  rw [deltaDivision_deltaClosure_eq_iSup_finiteRelations]
  change P ⊔ (⨆ N, deltaDivisionFiniteRelationIdeal D d a N) =
    ⨆ N, P ⊔ deltaDivisionFiniteRelationIdeal D d a (N + 1)
  apply le_antisymm
  · apply sup_le
    · exact (show P ≤ P ⊔ deltaDivisionFiniteRelationIdeal D d a (0 + 1) from le_sup_left).trans
        (le_iSup (fun N => P ⊔ deltaDivisionFiniteRelationIdeal D d a (N + 1)) 0)
    · apply iSup_le
      intro N
      exact (deltaDivisionFiniteRelationIdeal_mono D d a (Nat.le_succ N)).trans
        ((show deltaDivisionFiniteRelationIdeal D d a (N + 1) ≤
          P ⊔ deltaDivisionFiniteRelationIdeal D d a (N + 1) from le_sup_right).trans
          (le_iSup (fun N => P ⊔ deltaDivisionFiniteRelationIdeal D d a (N + 1)) N))
  · apply iSup_le
    intro N
    apply sup_le le_sup_left
    exact (le_iSup (deltaDivisionFiniteRelationIdeal D d a) (N + 1)).trans le_sup_right

/-- 逆Witt座標射による実際の全δ剰余イデアルの像は全段正規化イデアル。 -/
theorem deltaDivision_mod_pd_deltaClosure_inverse_map (D : DeltaStructure p A)
    (hpA : Function.Injective (fun b : A => (p : A) * b))
    (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    Ideal.map (relativeFreeWittInverseMap D hpA).toRingHom
      (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a)) =
      deltaDivisionInfiniteNormalizedPresentationIdeal D d a u := by
  rw [deltaDivision_mod_pd_deltaClosure_eq_iSup_finite, Ideal.map_iSup]
  unfold deltaDivisionInfiniteNormalizedPresentationIdeal
  congr 1
  funext N
  rw [deltaDivisionFiniteRelationIdeal_inverse_map_eq_first_sup_normalized D hpA hpL hg d a u hu,
    deltaDivisionFiniteNormalizedPresentationIdeal_map_initial D d a u hu]

/-- 実際のmod(p,d)全δ剰余商は、標準有限正規化商からの全段環に同型。 -/
def deltaDivision_mod_pd_deltaClosure_directLimitEquiv (D : DeltaStructure p A)
    (hpA : Function.Injective (fun b : A => (p : A) * b))
    (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) :
    (RelativeFreeDeltaRing (R := A) σ ⧸
      (Ideal.span {(p : RelativeFreeDeltaRing (R := A) σ), MvPolynomial.C d} ⊔
        (relativeFreeDeltaStructure σ D).deltaClosure (deltaDivisionRelationIdeal d a))) ≃+*
      DeltaDivisionFiniteNormalizedDirectLimit D d a u :=
  (Ideal.quotientEquiv _ _ (relativeFreeWittCoordinateEquiv D hpA).symm.toRingEquiv
    (deltaDivision_mod_pd_deltaClosure_inverse_map D hpA hpL hg d a u hu).symm).trans
    (deltaDivisionNormalizedDirectLimitQuotientEquiv D d a u)

/-- 実際の全δ剰余商の比較は、標準商射を逆Witt座標による具体的評価へ送る。 -/
theorem deltaDivision_mod_pd_deltaClosure_directLimitEquiv_mk (D : DeltaStructure p A)
    (hpA : Function.Injective (fun b : A => (p : A) * b))
    (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d)
    (f : RelativeFreeDeltaRing (R := A) σ) :
    deltaDivision_mod_pd_deltaClosure_directLimitEquiv D hpA hpL hg d a u hu
      (Ideal.Quotient.mk _ f) =
      deltaDivisionNormalizedDirectLimitEvaluation D d a u
        (relativeFreeWittInverseMap D hpA f) := by
  change deltaDivisionNormalizedDirectLimitQuotientEquiv D d a u
    (Ideal.Quotient.mk _ (relativeFreeWittInverseMap D hpA f)) = _
  exact deltaDivisionNormalizedDirectLimitQuotientEquiv_mk D d a u _

/-- 実際の全δ剰余商の比較は、基底係数の標準像を全段係数射へ送る。 -/
theorem deltaDivision_mod_pd_deltaClosure_directLimitEquiv_C (D : DeltaStructure p A)
    (hpA : Function.Injective (fun b : A => (p : A) * b))
    (hpL : Function.Injective (fun f : RelativeFreeDeltaRing (R := A) σ =>
      (p : RelativeFreeDeltaRing (R := A) σ) * f))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (d : A) (a : σ → A) (u : Aˣ) (hu : (u : A) = D.delta d) (b : A) :
    deltaDivision_mod_pd_deltaClosure_directLimitEquiv D hpA hpL hg d a u hu
      (Ideal.Quotient.mk _ (MvPolynomial.C b)) =
      deltaDivisionFiniteNormalizedDirectLimitBaseMap D d a u (Ideal.Quotient.mk _ b) := by
  rw [deltaDivision_mod_pd_deltaClosure_directLimitEquiv_mk]
  have hc : relativeFreeWittInverseMap (σ := σ) D hpA (MvPolynomial.C b) = MvPolynomial.C b :=
    AlgHom.commutes _ b
  rw [hc, deltaDivisionNormalizedDirectLimitEvaluation_C]

end SerrePositivity.BhattScholze
