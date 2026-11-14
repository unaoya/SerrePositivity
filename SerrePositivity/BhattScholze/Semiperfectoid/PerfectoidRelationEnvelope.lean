module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectoidPrismPresentation
public import SerrePositivity.BhattScholze.Semiperfectoid.PrismRelationQuotient
public import SerrePositivity.BhattScholze.Semiperfectoid.PerfectEnvelopeInitial

/-!
# Perfectoid 環の有限正則商の有界包絡と始性

## 概要
有界な有限 Koszul 正則商には、全有界試験 prism への始性を持つ実包絡が存在する。
## 方針
完全 prism に係数環を表示し、Example 7.9 と Lemma 4.8 を使う。
## 規約
BS 著者版 Proposition 7.10 の有限 T。零環も含み、標的に p 正則性を課さない。
## 使われ方
根付き有限関係の prismatic な模型。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open CategoryTheory Prismatic
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (S : Type u) [CommRing S]

/-- 概要：有界な有限正則商に対し、実際の有界包絡と全有界標的への始性を作る。
方針：完全 prism の剰余表示に関係を持ち上げ、K5 の存在と完全基底の一意持ち上げを使う。
規約：BS 著者版 Example 7.9・Proposition 7.10。標的は任意の有界 prism。
使われ方：有限 T の Δ との同定に先立つ古典的な始対象。 -/
theorem exists_perfectoidRelationEnvelope (hS : IsIntegralPerfectoid S p)
    {r : ℕ} (z : Fin r → S) (hz : IsKoszulResolution z)
    (hb : ∃ N : ℕ, ∀ (n : ℕ) (x : S ⧸ Ideal.span (Set.range z)),
      (p : S ⧸ Ideal.span (Set.range z))^n * x = 0 →
        (p : S ⧸ Ideal.span (Set.range z))^N * x = 0) :
    ∃ (A : CommRingCat.{u}) (P : OrientedPrism p A) (e : A ⧸ P.ideal ≃+* S)
      (w : Fin r → A),
      (∀ i, e (Ideal.Quotient.mk P.ideal (w i)) = z i) ∧
      P.deltaStructure.IsPerfect ∧
      ∃ (B : CommRingCat.{u}) (Q : OrientedPrism p B) (η : A →+* B),
        IsFiniteLciRelationEnvelope P w Q η ∧ IsBoundedPrism Q ∧
        ∃ v : S ⧸ Ideal.span (Set.range z) →+* B ⧸ Q.ideal,
          (∀ x : A, v (Ideal.Quotient.mk _ (e (Ideal.Quotient.mk P.ideal x))) =
            Ideal.Quotient.mk Q.ideal (η x)) ∧
          ∀ (C : Type u) [CommRing C] (Y : OrientedPrism p C) (hY : IsBoundedPrism Y)
            (s : S ⧸ Ideal.span (Set.range z) →+* C ⧸ Y.ideal),
            ∃! g : OrientedPrism.Hom Q Y, g.quotientMap.comp v = s := by
  obtain ⟨A, P, hP, _, ⟨e⟩⟩ := exists_boundedPerfectPrismPresentation p S hS
  have hlift (i : Fin r) : ∃ a : A, Ideal.Quotient.mk P.ideal a = e.symm (z i) :=
    Ideal.Quotient.mk_surjective _
  let w : Fin r → A := fun i => (hlift i).choose
  have hw (i : Fin r) : e (Ideal.Quotient.mk P.ideal (w i)) = z i := by
    rw [(hlift i).choose_spec, e.apply_symm_apply]
  let eT := prismRelationQuotientEquiv P e w z hw
  have hbound : ∃ N : ℕ, ∀ (n : ℕ) (x : A ⧸ (P.ideal ⊔ Ideal.span (Set.range w))),
      (p : A ⧸ (P.ideal ⊔ Ideal.span (Set.range w)))^n * x = 0 →
        (p : A ⧸ (P.ideal ⊔ Ideal.span (Set.range w)))^N * x = 0 := by
    obtain ⟨N, hN⟩ := hb
    refine ⟨N, fun n x hx => ?_⟩
    apply eT.injective
    have hx' : (p : S ⧸ Ideal.span (Set.range z))^n * eT x = 0 := by
      simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg eT hx
    simpa only [map_mul, map_pow, map_natCast, map_zero] using hN n (eT x) hx'
  obtain ⟨B, Q, η, hE, hQ⟩ := exists_bounded_lciRelationEnvelope P w
    (fun n => (prismRelation_isKoszulResolution P e w z hw hz).isZero _ (by omega)) hbound
  have hJ : P.ideal ≤ P.ideal ⊔ Ideal.span (Set.range w) := le_sup_left
  let v := (perfectEnvelopeResidueUnit hJ hE).comp eT.symm.toRingHom
  refine ⟨A, P, e, w, hw, hP, B, Q, η, hE, hQ, v, ?_, ?_⟩
  · intro x
    change perfectEnvelopeResidueUnit hJ hE
      (eT.symm (Ideal.Quotient.mk _ (e (Ideal.Quotient.mk P.ideal x)))) = _
    rw [← prismRelationQuotientEquiv_mk P e w z hw x]
    change perfectEnvelopeResidueUnit hJ hE (eT.symm (eT (Ideal.Quotient.mk _ x))) = _
    rw [eT.symm_apply_apply]
    rfl
  intro C _ Y hY s
  obtain ⟨g, hg, hgu⟩ := existsUnique_perfectEnvelopeHom hJ hE hP Y hY (s.comp eT.toRingHom)
  refine ⟨g, ?_, ?_⟩
  · apply RingHom.ext
    intro x
    exact (RingHom.congr_fun hg (eT.symm x)).trans (congrArg s (eT.apply_symm_apply x))
  · intro g' hg'
    apply hgu
    apply RingHom.ext
    intro x
    have h := RingHom.congr_fun hg' (eT x)
    change g'.quotientMap (perfectEnvelopeResidueUnit hJ hE (eT.symm (eT x))) = s (eT x) at h
    change g'.quotientMap (perfectEnvelopeResidueUnit hJ hE x) = s (eT x)
    simpa only [eT.symm_apply_apply] using h

end SerrePositivity.BhattScholze.Semiperfectoid
