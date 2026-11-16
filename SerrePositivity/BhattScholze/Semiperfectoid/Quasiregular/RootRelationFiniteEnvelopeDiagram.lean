module

public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootRelationFiniteAmbient
public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootRelationSubsetRaw
public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.AinfClassicalMaps
public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.PrismRelationQuotient
public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.FiniteEnvelopes.FiniteEnvelopeDiagram
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalCompletionUniformBound
/-!
# S′ の固定 A_inf 上の有限包絡全段

## 概要
任意の根付き変数族に対し、同じ A_inf 上で全有限初期関係の有界包絡を作る。
## 方針
全変数の持ち上げを先に選び、任意基底上の有限正則性と共通指数1を K5 に渡す。
## 規約
BS 著者版 Proposition 7.10。基底を有限部分族ごとに変更しない。
## 使われ方
S′ の生の包絡余極限と、その実完備化。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.SerrePositivity.BhattScholze.Andre _root_.SerrePositivity.DerivedCompletion _root_.SerrePositivity.BhattScholze.Prismatic _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (J : Type u)

/-- 概要：任意の根付き基底の固定 A_inf 上に、全有限初期関係の包絡図式の対象が存在。
方針：初期変数の共通持ち上げ、有限 Koszul 分解、指数1のねじれ評価、K5 を使う。
規約：BS 著者版 Proposition 7.10。各包絡の単位は同じ固定基底から来る。
使われ方：有限包絡の標準遷移と S′ の完備余極限。 -/
theorem exists_rootRelationFiniteEnvelopeDiagram (hR : IsIntegralPerfectoid R p) :
    let Base := rootFamilyBase p R J
    let hBase := rootFamilyBase_isIntegralPerfectoid p R J hR
    let P := ainfClassicalPrism p Base hBase
    ∃ w : J → ainfClassicalCoefficients p Base,
      (∀ j, ainfClassicalTheta p Base hBase (w j) = rootFamilyVariable p R J j 0) ∧
      ∃ (C : Finset J → CommRingCat.{u}) (Q : ∀ F, OrientedPrism p (C F))
        (η : ∀ F, ainfClassicalCoefficients p Base →+* C F),
        ∀ F, ∃ hE : IsPrismaticEnvelope P P.deltaStructure (RingHom.id _)
          P.deltaStructure.isDeltaHom_id (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F)
          (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal_generator P w F) (Q F) (η F),
          IsBoundedPrism (Q F) ∧
            (letI := (perfectEnvelopeResidueUnit
              (show P.ideal ≤ _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F from le_sup_left) hE).toAlgebra
             IsCompletelyFaithfullyFlat (Ideal.span {(p : ainfClassicalCoefficients p Base ⧸
               _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F)}) (C F ⧸ (Q F).ideal)) ∧
            (∀ (n : ℕ) (x : C F ⧸ (Q F).ideal),
              (p : C F ⧸ (Q F).ideal) ^n * x = 0 → (p : C F ⧸ (Q F).ideal) * x = 0) := by
  let Base := rootFamilyBase p R J
  let hBase := rootFamilyBase_isIntegralPerfectoid p R J hR
  let P := ainfClassicalPrism p Base hBase
  let A := ainfClassicalCoefficients p Base
  let e := ainfClassicalResidueEquiv p Base hBase
  have heθ (a : A) : e (Ideal.Quotient.mk P.ideal a) = ainfClassicalTheta p Base hBase a :=
    RingHom.congr_fun (ainfClassicalResidueEquiv_theta p Base hBase) a
  have hlift (j : J) : ∃ a : A, Ideal.Quotient.mk P.ideal a =
      e.symm (rootFamilyVariable p R J j 0) := Ideal.Quotient.mk_surjective _
  let w : J → A := fun j => (hlift j).choose
  have hw (j : J) : e (Ideal.Quotient.mk P.ideal (w j)) = rootFamilyVariable p R J j 0 := by
    rw [(hlift j).choose_spec, e.apply_symm_apply]
  have hreg (F : Finset J) : IsKoszulResolution
      (fun i => Ideal.Quotient.mk P.ideal (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRelations w F i)) := by
    let ι : Fin (Fintype.card F) → J := fun i => (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeEnumeration F i).val
    let z := rootRelationFiniteAmbientSequence p R J ι
    have hz : IsKoszulResolution z := rootRelationFiniteAmbient_isKoszulResolution p R J ι
      (Subtype.val_injective.comp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeEnumeration F).injective)
    have hwF (i) : e (Ideal.Quotient.mk P.ideal (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRelations w F i)) = z i := by
      change e (Ideal.Quotient.mk P.ideal (w (ι i))) = z i
      rw [hw]
      change rootFamilyVariable p R J (ι i) 0 =
        rootFamilyUnit p R J (rootFamilyPolynomialMap p R J (MvPolynomial.X (ι i)))
      rw [rootFamilyPolynomialMap_X_general]
      rfl
    have h := prismRelation_isKoszulResolution P e (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRelations w F) z hwF hz
    exact h
  have hb1 (F : Finset J) : ∀ (n : ℕ) (x : A ⧸ _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F),
      (p : A ⧸ _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F) ^n * x = 0 →
        (p : A ⧸ _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F) ^1 * x = 0 := by
    let ι : Fin (Fintype.card F) → J := fun i => (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeEnumeration F i).val
    let z := rootRelationFiniteAmbientSequence p R J ι
    have hwF (i) : e (Ideal.Quotient.mk P.ideal (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRelations w F i)) = z i := by
      change e (Ideal.Quotient.mk P.ideal (w (ι i))) = z i
      rw [hw]
      change rootFamilyVariable p R J (ι i) 0 =
        rootFamilyUnit p R J (rootFamilyPolynomialMap p R J (MvPolynomial.X (ι i)))
      rw [rootFamilyPolynomialMap_X_general]
      rfl
    have hi : (rootRelationSubsetRawIdeal p R J (Set.range ι)).map (rootFamilyUnit p R J) =
        Ideal.span (Set.range z) := by
      rw [← rootRelationFiniteAmbientRawIdeal_eq, Ideal.map_span, ← Set.range_comp]
      rfl
    let eI := Ideal.quotEquivOfEq hi
    let eRel := prismRelationQuotientEquiv P e (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRelations w F) z hwF
    have heI : P.ideal ⊔ Ideal.span (Set.range (_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRelations w F)) =
        _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F := by rw [_root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeRelations_ideal]; rfl
    let eT : (A ⧸ _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F) ≃+* rootRelationFiniteAmbientQuotient p R J ι :=
      (Ideal.quotEquivOfEq heI.symm).trans (eRel.trans eI.symm)
    intro n x hx
    apply eT.injective
    have hx' : (p : rootRelationFiniteAmbientQuotient p R J ι) ^n * eT x = 0 := by
      simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg eT hx
    simpa only [map_mul, map_pow, map_natCast, pow_one, map_zero] using
      rootRelationFiniteAmbientQuotient_torsion_bound_one p R J ι hR n (eT x) hx'
  obtain ⟨C, Q, η, hE⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_finiteEnvelopeDiagram P w hreg (fun F => ⟨1, hb1 F⟩)
  refine ⟨w, fun j => (heθ (w j)).symm.trans (hw j), C, Q, η, fun F => ?_⟩
  obtain ⟨hEF, hQF, hFF⟩ := hE F
  refine ⟨hEF, hQF, hFF, ?_⟩
  intro n x hx
  let b := perfectEnvelopeResidueUnit
    (show P.ideal ≤ _root_.SerrePositivity.BhattScholze.Semiperfectoid.finiteEnvelopeIdeal P w F from le_sup_left) hEF
  have hc : IsModuleComplete (C F ⧸ (Q F).ideal) (p : C F ⧸ (Q F).ideal)
      (ModuleCat.of _ (C F ⧸ (Q F).ideal)) :=
    isModuleComplete_principal_quotient_natCast (C F) p (Q F).generator (Q F).complete_p
  simpa only [pow_one] using completelyFlat_uniform_torsion_bound p b hc hFF.1 1 (hb1 F) n x hx

end SerrePositivity.BhattScholze.Semiperfectoid
