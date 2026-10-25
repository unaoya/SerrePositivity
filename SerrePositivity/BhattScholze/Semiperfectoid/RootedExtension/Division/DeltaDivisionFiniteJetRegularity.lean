module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionNormalizedAmbientSource
public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionWittJetRegularity

/-! # 元の相対自由δ環の具体的下位関係商における次段関係の正則性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A)
variable (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
variable (hpL : Function.Injective (fun z : RelativeFreeDeltaRing (R := A) σ ↦
  (p : RelativeFreeDeltaRing (R := A) σ) * z))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 1)
include hpA hpL hg hv

/-- 元の自由δ環の下位関係商内のWitt根関係は非零因子。 -/
theorem deltaDivisionFiniteWittRelation_quotient_isSMulRegular (s : σ) :
    IsSMulRegular (L₀ ⧸ I₀)
      (Ideal.Quotient.mk I₀ (deltaDivisionRelativeWittRelationElement D d a v s N)) := by
  let e := deltaDivisionFiniteNormalizedQuotientEquiv D hpA hpL hg d a v hv N
  have he : e (Ideal.Quotient.mk I₀ (deltaDivisionRelativeWittRelationElement D d a v s N)) =
      Ideal.Quotient.mk _ (relativeFreeFiniteInitialPolynomialMap (N + 2) σ A
        (deltaDivisionWittNormalizedPolynomial D d a v s N)) := by
    dsimp only [e]
    rw [deltaDivisionFiniteNormalizedQuotientEquiv_mk,
      deltaDivisionRelativeWittRelationElement_inverse_image D hpA hg]
  have hr := deltaDivisionNormalizedAmbientSource_relation_isSMulRegular D d a v N hv s
  intro x y hxy
  apply e.injective
  apply hr
  have h := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he] using h

/-- 元の自由δ環の下位関係商内で、次のN+2段のδ反復関係は非零因子。 -/
theorem deltaDivisionFiniteNextJet_quotient_isSMulRegular (s : σ) :
    IsSMulRegular (L₀ ⧸ I₀)
      (Ideal.Quotient.mk I₀ (deltaDivisionIteratedRelation D d a s (N + 2))) := by
  let E := relativeFreeDeltaStructure σ D
  let vL := v.map (MvPolynomial.C : A →+* L₀).toMonoidHom
  have hvL : (vL : L₀) = E.delta (MvPolynomial.C d) := by
    change MvPolynomial.C (v : A) = (relativeFreeDeltaStructure σ D).delta (MvPolynomial.C d)
    rw [hv, relativeFreeDeltaStructure_delta_C]
  have hpI : (p : L₀) ∈ I₀ :=
    (show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ I₀ from le_sup_left)
      (Ideal.subset_span (by simp))
  have hdI : MvPolynomial.C d ∈ I₀ :=
    (show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ I₀ from le_sup_left)
      (Ideal.subset_span (by simp))
  have hlower : ∀ i ≤ N + 1,
      E.delta^[i] (MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s)) ∈ I₀ := by
    intro i hi
    apply (show deltaDivisionFiniteRelationIdeal D d a (N + 1) ≤ I₀ from le_sup_right)
    apply Ideal.subset_span
    exact Set.mem_range.mpr ⟨(s, ⟨i, by omega⟩), rfl⟩
  exact (deltaDivision_next_jet_quotient_isSMulRegular_iff_witt E hpL hg I₀ hpI
    (MvPolynomial.C d) (MvPolynomial.X (s, 0)) (MvPolynomial.C (a s)) hdI vL hvL N hlower).mpr
    (deltaDivisionFiniteWittRelation_quotient_isSMulRegular D hpA hpL hg d a v hv N s)

/-- 元の次段δ反復関係の具体的商上のKoszul分解。添字σの有限性は不要。 -/
theorem deltaDivisionFiniteNextJet_quotient_isKoszulResolution (s : σ) :
    SerrePositivity.IsKoszulResolution (fun _ : Fin 1 ↦
      Ideal.Quotient.mk I₀ (deltaDivisionIteratedRelation D d a s (N + 2))) := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  rw [List.ofFn_const, List.replicate_one,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact deltaDivisionFiniteNextJet_quotient_isSMulRegular D hpA hpL hg d a v hv N s

/-- 元の次段δ反復関係による導来商は実Koszul錐関手と自然同型。 -/
def deltaDivisionFiniteNextJet_derivedKoszulNatIso (s : σ) :
    boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span
        {Ideal.Quotient.mk I₀ (deltaDivisionIteratedRelation D d a s (N + 2))})) ⋙
      boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span
        {Ideal.Quotient.mk I₀ (deltaDivisionIteratedRelation D d a s (N + 2))})) ⋙
      DerivedCategory.Minus.ι ≅
    DerivedCategory.Minus.ι ⋙ DerivedCompletion.derivedScalarConeFunctor (L₀ ⧸ I₀)
      (Ideal.Quotient.mk I₀ (deltaDivisionIteratedRelation D d a s (N + 2))) :=
  restrictedDerivedQuotientKoszulNatIso _
    (deltaDivisionFiniteNextJet_quotient_isSMulRegular D hpA hpL hg d a v hv N s)

end SerrePositivity.BhattScholze
