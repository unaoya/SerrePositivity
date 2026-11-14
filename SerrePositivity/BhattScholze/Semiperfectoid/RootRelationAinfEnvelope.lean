module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Semiperfectoid.AinfClassicalMaps
public import SerrePositivity.BhattScholze.Semiperfectoid.RootRelationLiftInitial

/-!
# 固定 A_inf 上の有限根関係包絡

## 概要
drafts と同じ固定 A_inf と ULift 表示の有限 T に、有界な実 lci 包絡を作る。
## 方針
既存の正則性と有界性を移し、K5 の包絡と Lemma 4.8 の一意持ち上げを使う。
## 規約
BS 著者版 Example 7.9・Proposition 7.10。Δ との同定は含めない。
## 使われ方
regularSemiperfectoid_prismatic の envelope と始性の古典的な部分。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open DerivedCompletion Prismatic CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] {r : ℕ} (f : Fin r → R)

/-- ULift 関係商の実完備化は、通常商に標準単位を戻す環同型を持つ。 -/
theorem exists_rootLiftCompletionOrdinaryEquiv :
    ∃ e : CompletedRing p (rootLiftRelationQuotient p R f) ≃+* rootLiftRelationQuotient p R f,
      ∀ x : rootFamilyBase p R (ULift.{u} (Fin r)),
        e ((principalCompletionRingCatUnit p (CommRingCat.of (rootLiftRelationQuotient p R f))).hom
          (Ideal.Quotient.mk _ x)) = Ideal.Quotient.mk _ x := by
  obtain ⟨eD, heD⟩ := exists_rootRelationLiftCompletionEquiv p R f
  let eL := rootRelationLiftQuotientEquiv p R f
  refine ⟨eD.symm.trans eL, fun x => ?_⟩
  have hx := heD ((rootFamilyFiniteLiftEquiv p R).symm x)
  rw [(rootFamilyFiniteLiftEquiv p R).apply_symm_apply] at hx
  change eL (eD.symm _) = _
  rw [← hx, eD.symm_apply_apply, rootRelationLiftQuotientEquiv_mk,
    (rootFamilyFiniteLiftEquiv p R).apply_symm_apply]

/-- 概要：固定 A_inf 上で有限 T の実 lci 包絡・忠実平坦な単位・全有界標的への始性を作る。
方針：Xi−fi の正則性と有界性を固定剰余表示へ移し、K5 と Lemma 4.8 を再利用する。
規約：BS 著者版 Proposition 7.10 の古典的な有限 T。零環も含む。
使われ方：drafts の regularSemiperfectoid_prismatic の実包絡側。 -/
theorem exists_rootRelationAinfEnvelope (hR : IsIntegralPerfectoid R p) :
    let Base := rootFamilyBase p R (ULift.{u} (Fin r))
    let hBase := rootFamilyBase_isIntegralPerfectoid p R (ULift.{u} (Fin r)) hR
    let P := ainfClassicalPrism p Base hBase
    let T := CompletedRing p (rootLiftRelationQuotient p R f)
    ∃ w : Fin r → ainfClassicalCoefficients p Base,
      (∀ i, ainfClassicalTheta p Base hBase (w i) = rootLiftRelation p R f (ULift.up i)) ∧
      ∃ (B : CommRingCat.{u}) (Q : OrientedPrism p B) (η : ainfClassicalCoefficients p Base →+* B),
        IsFiniteLciRelationEnvelope P w Q η ∧ IsBoundedPrism Q ∧
        ∃ v : T →+* B ⧸ Q.ideal,
          (∀ x, v ((principalCompletionRingCatUnit p (CommRingCat.of (rootLiftRelationQuotient p R f))).hom
              (Ideal.Quotient.mk _ (ainfClassicalTheta p Base hBase x))) =
            Ideal.Quotient.mk Q.ideal (η x)) ∧
          (letI := v.toAlgebra
           IsCompletelyFaithfullyFlat (Ideal.span {(p : T)}) (B ⧸ Q.ideal)) ∧
          ∀ (C : Type u) [CommRing C] (Y : OrientedPrism p C) (hY : IsBoundedPrism Y)
            (s : T →+* C ⧸ Y.ideal),
            ∃! g : OrientedPrism.Hom Q Y, g.quotientMap.comp v = s := by
  let Base := rootFamilyBase p R (ULift.{u} (Fin r))
  let hBase := rootFamilyBase_isIntegralPerfectoid p R (ULift.{u} (Fin r)) hR
  let P := ainfClassicalPrism p Base hBase
  let A := ainfClassicalCoefficients p Base
  let e := ainfClassicalResidueEquiv p Base hBase
  let z : Fin r → Base := fun i => rootLiftRelation p R f (ULift.up i)
  have hz : IsKoszulResolution z := by
    have h := (rootRelationSequence_isKoszulResolution p R f).map_ringEquiv (rootFamilyFiniteLiftEquiv p R)
    have he : (rootFamilyFiniteLiftEquiv p R) ∘ rootRelationSequence p R f = z := by
      funext i
      exact rootFamilyFiniteLiftEquiv_relation p R f i
    rwa [he] at h
  have hlift (i : Fin r) : ∃ a : A, Ideal.Quotient.mk P.ideal a = e.symm (z i) :=
    Ideal.Quotient.mk_surjective _
  let w : Fin r → A := fun i => (hlift i).choose
  have hw (i : Fin r) : e (Ideal.Quotient.mk P.ideal (w i)) = z i := by
    rw [(hlift i).choose_spec, e.apply_symm_apply]
  have hθ (x : A) : e (Ideal.Quotient.mk P.ideal x) = ainfClassicalTheta p Base hBase x :=
    RingHom.congr_fun (ainfClassicalResidueEquiv_theta p Base hBase) x
  let eI : rootLiftRelationQuotient p R f ≃+* Base ⧸ Ideal.span (Set.range z) :=
    Ideal.quotEquivOfEq (rootLiftRelationIdeal_eq p R f)
  let eRel := prismRelationQuotientEquiv P e w z hw
  let eS := eI.trans eRel.symm
  let eOld := (rootRelationLiftQuotientEquiv p R f).trans eS
  have hbound : ∃ N : ℕ, ∀ (n : ℕ) (x : A ⧸ (P.ideal ⊔ Ideal.span (Set.range w))),
      (p : A ⧸ (P.ideal ⊔ Ideal.span (Set.range w)))^n * x = 0 →
        (p : A ⧸ (P.ideal ⊔ Ideal.span (Set.range w)))^N * x = 0 := by
    obtain ⟨N, hN⟩ := rootRelationQuotient_bounded p R f hR
    refine ⟨N, fun n x hx => ?_⟩
    apply eOld.symm.injective
    have hx' : (p : rootRelationQuotient p R f)^n * eOld.symm x = 0 := by
      simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg eOld.symm hx
    simpa only [map_mul, map_pow, map_natCast, map_zero] using hN n (eOld.symm x) hx'
  obtain ⟨B, Q, η, hE, hQ, hFF⟩ := exists_bounded_lciRelationEnvelope_faithful P w
    (fun n => (prismRelation_isKoszulResolution P e w z hw hz).isZero _ (by omega)) hbound
  obtain ⟨eD, heD⟩ := exists_rootLiftCompletionOrdinaryEquiv p R f
  let eT := eD.trans eS
  have hJ : P.ideal ≤ P.ideal ⊔ Ideal.span (Set.range w) := le_sup_left
  let b := perfectEnvelopeResidueUnit hJ hE
  let v := b.comp eT.toRingHom
  refine ⟨w, fun i => (hθ (w i)).symm.trans (hw i), B, Q, η, hE, hQ, v, ?_, ?_, ?_⟩
  · intro x
    change b (eS (eD _)) = _
    rw [heD]
    have heS : eS (Ideal.Quotient.mk _ (ainfClassicalTheta p Base hBase x)) =
        Ideal.Quotient.mk _ x := by
      apply eRel.injective
      change eRel (eRel.symm (eI (Ideal.Quotient.mk _ (ainfClassicalTheta p Base hBase x)))) = _
      rw [eRel.apply_symm_apply, Ideal.quotEquivOfEq_mk, prismRelationQuotientEquiv_mk, hθ]
    rw [heS]
    rfl
  · have hsrc : letI := eT.toRingHom.toAlgebra
        IsCompletelyFaithfullyFlat
          (Ideal.span {(p : CompletedRing p (rootLiftRelationQuotient p R f))})
          (A ⧸ (P.ideal ⊔ Ideal.span (Set.range w))) := by
      letI := eT.toRingHom.toAlgebra
      letI : Module.FaithfullyFlat (CompletedRing p (rootLiftRelationQuotient p R f))
          (A ⧸ (P.ideal ⊔ Ideal.span (Set.range w))) := by
        apply RingHom.faithfullyFlat_algebraMap_iff.mp
        exact RingHom.FaithfullyFlat.of_bijective eT.bijective
      exact isCompletelyFaithfullyFlat_of_faithfullyFlat _
    exact Andre.Transfinite.isCompletelyFaithfullyFlat_comp eT.toRingHom b _ hsrc (by
      simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hFF)
  · intro C _ Y hY s
    exact existsUnique_prismHom_of_source_equiv Q Y b eT
      (fun z => existsUnique_perfectEnvelopeHom hJ hE (ainfClassicalPrism_perfect p Base hBase) Y hY z) s

end SerrePositivity.BhattScholze.Semiperfectoid

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Prop 7.10" (partial := component) "BS-W17 H5（11-12）：T（有限）と S′（任意添字）の古典的な部分は本体：固定 A_inf 上の有界な実包絡、全有界 prism への一意な射、S′ の完全化と Cor 7.3 の単位を保つ唯一の同型（停止点 4・5a・5）。S′ の単位の完全忠実平坦性は後回し（E3 は使わない）。Δ_R/A との同定（G10）は drafts ／ 11-12 節の見直し：S′ の部分は f_j=0 の場合（根の商）だけ"] _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_rootRelationAinfEnvelope
