module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Semiperfectoid.RootRelationFiniteEnvelopeDiagram
public import SerrePositivity.BhattScholze.Semiperfectoid.PrismInitialCompletion
public import SerrePositivity.BhattScholze.Semiperfectoid.PrismInitialCompletion
public import SerrePositivity.BhattScholze.Semiperfectoid.FiniteEnvelopes.FiniteEnvelopeCompletion
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
/-!
# S′ の実完備包絡と全有界標的への始性

## 概要
任意の根付き変数族の初期変数を零にした商の実 p 完備化上に、有界な始的 prism を作る。
## 方針
固定 A_inf 上の有限包絡の実完備余極限を使い、剰余単位を実完備化へ一意に延長する。
## 規約
BS 著者版 Proposition 7.10。零環を含み、標的を p 正則な prism に狭めない。
## 使われ方
E3 の S′ と、その初期包絡の完全化の比較。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open CategoryTheory DerivedCompletion Prismatic
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (J : Type u)

/-- 概要：S′ の実完備化上に、固定 A_inf からの有界包絡と全有界標的への一意な射がある。
方針：全有限段の共通指数1で完備余極限を作り、通常商の始性を実 p 完備化へ移す。
規約：BS 著者版 Proposition 7.10。指定した θ と剰余単位の対応を結論に含む。
使われ方：S′ の初期包絡と Corollary 7.3 の完全化比較。 -/
theorem exists_rootRelationCompletedInitial (hR : IsIntegralPerfectoid R p) :
    let Base := rootFamilyBase p R J
    let hBase := rootFamilyBase_isIntegralPerfectoid p R J hR
    let P := ainfClassicalPrism p Base hBase
    let T := Base ⧸ Ideal.span (Set.range fun j => rootFamilyVariable p R J j 0)
    let S' := CompletedRing p T
    ∃ (w : J → ainfClassicalCoefficients p Base),
      (∀ j, ainfClassicalTheta p Base hBase (w j) = rootFamilyVariable p R J j 0) ∧
      ∃ (B : CommRingCat.{u}) (V : OrientedPrism p B) (ν : ainfClassicalCoefficients p Base →+* B),
        IsBoundedPrism V ∧
        IsPrismaticEnvelope P P.deltaStructure (RingHom.id _) P.deltaStructure.isDeltaHom_id
          (P.ideal ⊔ Ideal.span (Set.range w))
          ((show P.ideal ≤ P.ideal ⊔ Ideal.span (Set.range w) from le_sup_left)
            (Ideal.subset_span (Set.mem_singleton _))) V ν ∧
        ∃ v : S' →+* B ⧸ V.ideal,
          (∀ x, v ((principalCompletionRingCatUnit p (CommRingCat.of T)).hom
              (Ideal.Quotient.mk _ (ainfClassicalTheta p Base hBase x))) =
            Ideal.Quotient.mk V.ideal (ν x)) ∧
          ∀ (C : Type u) [CommRing C] (Y : OrientedPrism p C) (hY : IsBoundedPrism Y)
            (s : S' →+* C ⧸ Y.ideal), ∃! g : OrientedPrism.Hom V Y, g.quotientMap.comp v = s := by
  let Base := rootFamilyBase p R J
  let hBase := rootFamilyBase_isIntegralPerfectoid p R J hR
  let P := ainfClassicalPrism p Base hBase
  let A := ainfClassicalCoefficients p Base
  let e := ainfClassicalResidueEquiv p Base hBase
  let T := Base ⧸ Ideal.span (Set.range fun j => rootFamilyVariable p R J j 0)
  have heθ (x : A) : e (Ideal.Quotient.mk P.ideal x) = ainfClassicalTheta p Base hBase x :=
    RingHom.congr_fun (ainfClassicalResidueEquiv_theta p Base hBase) x
  obtain ⟨w, hw, C, Q, η, hF⟩ := exists_rootRelationFiniteEnvelopeDiagram p R J hR
  choose hE hQ hFF hN using hF
  let L := FiniteEnvelopeRawColimit P w C Q η hE
  let d := finiteEnvelopeRawColimitBase P w C Q η hE P.generator
  letI := pdCompletionCommRing L p d
  obtain ⟨V, hV, hEnv⟩ := exists_boundedFiniteEnvelopeCompletion P w C Q η hE 1
    (fun F n x hx => by simpa only [pow_one] using hN F n x hx)
  let B := PDCompletionH0 L p d
  let ν : A →+* B := (pdCompletionUnit L p d).comp (finiteEnvelopeRawColimitBase P w C Q η hE)
  have hw' (j : J) : e (Ideal.Quotient.mk P.ideal (w j)) = rootFamilyVariable p R J j 0 := by
    exact (heθ (w j)).trans (hw j)
  let eT := prismRelationFamilyQuotientEquiv P e w (fun j => rootFamilyVariable p R J j 0) hw'
  let v₀ : T →+* B ⧸ V.ideal :=
    (perfectEnvelopeResidueUnit (show P.ideal ≤ P.ideal ⊔ Ideal.span (Set.range w) from le_sup_left)
      hEnv).comp eT.symm.toRingHom
  have hi : ∀ (C' : Type u) [CommRing C'] (Y : OrientedPrism p C') (hY : IsBoundedPrism Y)
      (s : T →+* C' ⧸ Y.ideal), ∃! g : OrientedPrism.Hom V Y, g.quotientMap.comp v₀ = s := by
    intro C' _ Y hY s
    exact existsUnique_prismHom_of_source_equiv V Y
      (perfectEnvelopeResidueUnit (show P.ideal ≤ P.ideal ⊔ Ideal.span (Set.range w) from le_sup_left) hEnv)
      eT.symm (fun z => existsUnique_perfectEnvelopeHom
        (show P.ideal ≤ P.ideal ⊔ Ideal.span (Set.range w) from le_sup_left) hEnv
        (ainfClassicalPrism_perfect p Base hBase) Y hY z) s
  obtain ⟨v, hv, hinit⟩ := exists_initialPrismUnit_on_completion V v₀ hi
  refine ⟨w, hw, CommRingCat.of B, V, ν, hV, hEnv, v, ?_, hinit⟩
  intro x
  have heT : eT (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (ainfClassicalTheta p Base hBase x) := by
    rw [prismRelationFamilyQuotientEquiv_mk]
    exact congrArg (Ideal.Quotient.mk _) (heθ x)
  rw [← heT]
  have hvx := RingHom.congr_fun hv (eT (Ideal.Quotient.mk _ x))
  change v ((principalCompletionRingCatUnit p (CommRingCat.of T)).hom
    (eT (Ideal.Quotient.mk _ x))) =
      perfectEnvelopeResidueUnit
        (show P.ideal ≤ P.ideal ⊔ Ideal.span (Set.range w) from le_sup_left) hEnv
        (eT.symm (eT (Ideal.Quotient.mk _ x))) at hvx
  rw [eT.symm_apply_apply] at hvx
  exact hvx

end SerrePositivity.BhattScholze.Semiperfectoid

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Prop 7.10" (partial := component) "BS-W17 H5（11-12）：T（有限）と S′（任意添字）の古典的な部分は本体：固定 A_inf 上の有界な実包絡、全有界 prism への一意な射、S′ の完全化と Cor 7.3 の単位を保つ唯一の同型（停止点 4・5a・5）。S′ の単位の完全忠実平坦性は後回し（E3 は使わない）。Δ_R/A との同定（G10）は drafts ／ 11-12 節の見直し：S′ の部分は f_j=0 の場合（根の商）だけ"] _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_rootRelationCompletedInitial
