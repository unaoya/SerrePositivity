module

public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.CompletedTensorFaithful
public import SerrePositivity.BhattScholze.Semiperfectoid.Lci.CompletedTensorRelationResidue
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 関係商上の完備テンソル剰余の完全忠実平坦性

## 概要
prism の剰余が関係商上 p 完全忠実平坦なら、有界な係数関係商への完備底変換も同じ性質を持つ。
## 方針
実剰余のテンソル比較を、指定した単位に沿って線形化する。
## 規約
BS 著者版 Example 7.9・Proposition 7.10。係数の p 正則性を仮定しない。
## 使われ方
有限 T の lci 包絡の単位。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.SerrePositivity.DerivedCompletion _root_.SerrePositivity.BhattScholze.Prismatic
open scoped _root_.TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {U A E : Type u}
  [CommRing U] [CommRing A] [CommRing E] [Algebra U A] [Algebra U E]

/-- 関係商への完備底変換の生成元剰余に、係数を保つ完全忠実平坦な単位が存在する。 -/
theorem exists_prismCompletedTensor_relationResidue_faithful (Q : OrientedPrism p E)
    (K : Ideal U) (hK : K.map (algebraMap U E) ≤ Q.ideal)
    (hE : letI := quotientFactorAlgebra U E K Q.ideal hK
      IsCompletelyFaithfullyFlat (Ideal.span {(p : U ⧸ K)}) (E ⧸ Q.ideal))
    (hA : ∃ N : ℕ, ∀ (n : ℕ) (x : A ⧸ K.map (algebraMap U A)),
      (p : A ⧸ K.map (algebraMap U A))^n * x = 0 →
        (p : A ⧸ K.map (algebraMap U A))^N * x = 0) :
    let H := PrismCompletedTensor (A := U) (C := A) Q
    ∃ v : (A ⧸ K.map (algebraMap U A)) →+*
        H ⧸ Ideal.span {prismCompletedTensorLeft Q Q.generator},
      (∀ a : A, v (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (prismCompletedTensorRight Q a)) ∧
      letI := v.toAlgebra
      IsCompletelyFaithfullyFlat (Ideal.span {(p : A ⧸ K.map (algebraMap U A))})
        (H ⧸ Ideal.span {prismCompletedTensorLeft Q Q.generator}) := by
  letI := quotientFactorAlgebra U E K Q.ideal hK
  letI := adicQuotientAlgebra K A
  let S := A ⧸ K.map (algebraMap U A)
  let V := S ⊗[U ⧸ K] (E ⧸ Q.ideal)
  let H := PrismCompletedTensor (A := U) (C := A) Q
  let W := H ⧸ Ideal.span {prismCompletedTensorLeft Q Q.generator}
  obtain ⟨e, he⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_prismCompletedTensor_relationResidue_equiv (A := A) Q K hK
  let j := (principalCompletionRingCatUnit p (CommRingCat.of V)).hom
  let η : S →+* CompletedRing p V := j.comp (algebraMap S V)
  let v : S →+* W := e.symm.toRingHom.comp η
  letI : Algebra S (CompletedRing p V) := η.toAlgebra
  letI : Algebra S W := v.toAlgebra
  refine ⟨v, ?_, ?_⟩
  · intro a
    apply e.injective
    change e (e.symm (η (Ideal.Quotient.mk _ a))) = _
    rw [e.apply_symm_apply, he]
    rfl
  · have hV : IsCompletelyFaithfullyFlat (Ideal.span {(p : S)}) (CompletedRing p V) :=
      completedTensorPrincipal_isCompletelyFaithfullyFlat (U ⧸ K) S (E ⧸ Q.ideal) p hE hA
    let eS : W ≃ₐ[S] CompletedRing p V := AlgEquiv.ofRingEquiv (f := e)
      (fun s => e.apply_symm_apply (η s))
    exact isCompletelyFaithfullyFlat_of_linearEquiv _ eS.symm.toLinearEquiv hV

end SerrePositivity.BhattScholze.Semiperfectoid
