module

public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootRelationLift
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionLinearMap

/-!
# ULift 添字の実完備な有限 T の始性

## 概要
drafts と同じ ULift 関係商の実完備化に、完全忠実平坦な単位と全有界試験 prism への始性を返す。
## 方針
通常の有限 T との単位を保つ環同型に沿って、既存の包絡と普遍性を移す。
## 規約
BS 著者版 Proposition 7.10。Δ との同定は含めず、標的の p 正則性を要求しない。
## 使われ方
regularSemiperfectoid の古典的な包絡模型。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.SerrePositivity.DerivedCompletion _root_.SerrePositivity.BhattScholze.Prismatic _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] {r : ℕ} (f : Fin r → R)

/-- 実 H⁰ と環圏の完備化の表示も含めた、有限 T の単位を保つ比較。 -/
theorem exists_rootRelationLiftCompletionEquiv :
    ∃ e : rootRelationQuotient p R f ≃+* CompletedRing p (rootLiftRelationQuotient p R f),
      ∀ x : rootFamilyBase p R (Fin r),
        e (rootRelationQuotientUnit p R f x) =
          (principalCompletionRingCatUnit p (CommRingCat.of (rootLiftRelationQuotient p R f))).hom
            (Ideal.Quotient.mk _ (rootFamilyFiniteLiftEquiv p R x)) := by
  let eC : rootLiftRelationCompletion p R f ≃+* CompletedRing p (rootLiftRelationQuotient p R f) := by
    change rootLiftRelationCompletion p R f ≃+* rootLiftRelationCompletion p R f
    exact RingEquiv.refl _
  refine ⟨(rootRelationLiftCompletionEquiv p R f).trans eC, fun x => ?_⟩
  change eC (rootRelationLiftCompletionEquiv p R f (rootRelationQuotientUnit p R f x)) = _
  rw [rootRelationLiftCompletionEquiv_unit]
  rfl

/-- 概要：ULift 表示の実完備な有限 T に、忠実平坦な単位と全有界標的への始性を作る。
方針：通常の有限 T の実包絡を、実完備化までの単位を保つ比較に沿って移す。
規約：BS 著者版 Proposition 7.10 の古典的な部分。零環の枝を含む。
使われ方：drafts の regularSemiperfectoid から prismatic な包絡の比較 の同定へ渡す模型。 -/
theorem exists_rootLiftRelationCompletion_initial (hR : IsIntegralPerfectoid R p) :
    let T := CompletedRing p (rootLiftRelationQuotient p R f)
    ∃ (B : CommRingCat.{u}) (Q : OrientedPrism p B) (v : T →+* B ⧸ Q.ideal),
      IsBoundedPrism Q ∧
      (letI := v.toAlgebra
       IsCompletelyFaithfullyFlat (Ideal.span {(p : T)}) (B ⧸ Q.ideal)) ∧
      ∀ (C : Type u) [CommRing C] (Y : OrientedPrism p C) (hY : IsBoundedPrism Y)
        (s : T →+* C ⧸ Y.ideal),
        ∃! g : OrientedPrism.Hom Q Y, g.quotientMap.comp v = s := by
  obtain ⟨A, P, e, w, hw, hP, B, Q, η, hE, hQ, v, hv, hFF, hinit⟩ :=
    exists_rootRelationEnvelope_faithful p R f hR
  obtain ⟨eT, _⟩ := exists_rootRelationLiftCompletionEquiv p R f
  let v' := v.comp eT.symm.toRingHom
  refine ⟨B, Q, v', hQ, ?_, ?_⟩
  · have hsrc : letI := eT.symm.toRingHom.toAlgebra
        IsCompletelyFaithfullyFlat
          (Ideal.span {(p : CompletedRing p (rootLiftRelationQuotient p R f))})
          (rootRelationQuotient p R f) := by
      letI := eT.symm.toRingHom.toAlgebra
      letI : Module.FaithfullyFlat (CompletedRing p (rootLiftRelationQuotient p R f))
          (rootRelationQuotient p R f) := by
        apply RingHom.faithfullyFlat_algebraMap_iff.mp
        exact RingHom.FaithfullyFlat.of_bijective eT.symm.bijective
      exact isCompletelyFaithfullyFlat_of_faithfullyFlat _
    exact Andre.Transfinite.isCompletelyFaithfullyFlat_comp eT.symm.toRingHom v _ hsrc (by
      simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hFF)
  · intro C _ Y hY s
    exact existsUnique_prismHom_of_source_equiv Q Y v eT.symm (hinit C Y hY) s

end SerrePositivity.BhattScholze.Semiperfectoid
