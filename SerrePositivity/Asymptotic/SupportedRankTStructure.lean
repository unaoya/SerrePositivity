module

public import SerrePositivity.Asymptotic.SupportedSequenceTStructure
public import SerrePositivity.Asymptotic.SmallRankHomologicalKernel
public import SerrePositivity.CategoryTheory.HomologicalKernelTStructure

/-!
# 支持つきランク商の有界 t 構造と冪等完備性

ランクの小さい部分圏をホモロジー関手の核と同定し、
切り詰めによる分母の保存を導く。商の有界 t 構造から冪等完備性を得る。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Idempotents IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A] {s : ℕ → ℕ}
  [HasDerivedCategory (ModuleCat.{u} A)] {e : ℕ} (z : Fin e → A)
  (K : CochainComplex (ModuleCat.{u} A) ℤ)
  (hK : IsResolutionOf K (ModuleCat.of A (A ⧸ maximalIdeal A)))
  (hKf : ∀ i, Module.Free A (K.X i)) (hKn : ∀ i, Module.Finite A (K.X i))
  (d : ℕ) (hKb : ∀ i, i < -(d : ℤ) → IsZero (K.X i))
  (hfg : (Ideal.span (Set.range z)).FG)
  (hfin : ∀ v : ℕ, 0 < v → ∀ q : ℤ,
    (ordinaryLengthOnIdeal (Ideal.span (Set.range z))).len
      ((koszulComplex (fun j ↦ z j ^ v)).homology q) ≠ ⊤)

omit [IsLocalRing A] in
/-- 各段のホモロジーが零なら、長さの商へのホモロジーも零。 -/
lemma supportedSequenceSmallHomology_isZero_of_derived
    (X : (supportedSequence (s := s) z).FullSubcategory) (q : ℤ)
    (hz : ∀ n, IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) q).obj
      ((supportedDerivedEvaluation z n).obj X))) :
    IsZero ((supportedSequenceSmallHomology (ordinaryLengthOnIdeal (Ideal.span (Set.range z)))
      hfg z Ideal.le_radical hfin q).obj X) := by
  apply (supportedSequenceSmallHomology_isZero_iff _ hfg z Ideal.le_radical hfin X q).2
  apply (smallLengthFamily _ s).prop_of_isZero
  apply IsZero.of_iso ?_ (supportedDerivedHomologyIso z X q).symm
  rw [IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext n
  exact (hz n.as).eq_of_src _ _

/-- 非正側から一段離れた対象の第零ホモロジーは消える。 -/
lemma supportedSmallHomology_zero_of_isLE
    (X : (supportedSequence (s := s) z).FullSubcategory)
    (hX : (supportedSequenceTStructure z K hK hKf hKn d hKb hfg hfin).IsLE X (-1)) :
    IsZero ((supportedSequenceSmallHomology (ordinaryLengthOnIdeal (Ideal.span (Set.range z)))
      hfg z Ideal.le_radical hfin 0).obj X) := by
  apply supportedSequenceSmallHomology_isZero_of_derived z hfg hfin X 0
  intro n
  have : ((supportedDerivedEvaluation z n).obj X).IsLE (-1) := ⟨hX.le n⟩
  exact DerivedCategory.isZero_of_isLE _ (-1) 0 (by omega)

/-- 正の側の対象の第零ホモロジーは消える。 -/
lemma supportedSmallHomology_zero_of_isGE
    (X : (supportedSequence (s := s) z).FullSubcategory)
    (hX : (supportedSequenceTStructure z K hK hKf hKn d hKb hfg hfin).IsGE X 1) :
    IsZero ((supportedSequenceSmallHomology (ordinaryLengthOnIdeal (Ideal.span (Set.range z)))
      hfg z Ideal.le_radical hfin 0).obj X) := by
  apply supportedSequenceSmallHomology_isZero_of_derived z hfg hfin X 0
  intro n
  have : ((supportedDerivedEvaluation z n).obj X).IsGE 1 := ⟨hX.ge n⟩
  exact DerivedCategory.isZero_of_isGE _ 1 0 (by omega)

/-- 支持つきランク商の分母は、構成した t 構造の非正切り詰めで保たれる。 -/
theorem supportedRank_truncLE_denominator
    {X Y : (supportedSequence (s := s) z).FullSubcategory} (f : X ⟶ Y)
    (hf : (rankSmallBounded.inverseImage (supportedSequence z).ι).trW f) :
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW
      (((supportedSequenceTStructure z K hK hKf hKn d hKb hfg hfin).truncLE 0).map f) := by
  rw [rankSmall_eq_homologicalKernel z K hK hKf hKn d hKb hfg hfin] at hf ⊢
  exact homologicalKernel_truncLE _ _
    (supportedSmallHomology_zero_of_isLE z K hK hKf hKn d hKb hfg hfin)
    (supportedSmallHomology_zero_of_isGE z K hK hKf hKn d hKb hfg hfin) f hf

/-- 支持つき自由列のランク商上の有界 t 構造。 -/
noncomputable def supportedRankTStructure :
    TStructure (SupportedSequenceRankQuotient (s := s) z) :=
  verdierTStructure (supportedSequenceTStructure z K hK hKf hKn d hKb hfg hfin)
    (rankSmallBounded.inverseImage (supportedSequence z).ι)
    (fun _ _ f hf ↦ supportedRank_truncLE_denominator z K hK hKf hKn d hKb hfg hfin f hf)

/-- 商の t 構造の有界性。 -/
lemma supportedRankTStructure_bounded (Y : SupportedSequenceRankQuotient (s := s) z) :
    (supportedRankTStructure z K hK hKf hKn d hKb hfg hfin).bounded Y :=
  verdierTStructure_bounded _ _ _
    (supportedSequenceTStructure_bounded z K hK hKf hKn d hKb hfg hfin) Y

include hK hKf hKn hKb hfg hfin in
/-- 支持つきランク商は、既に冪等完備である。 -/
theorem supportedRank_isIdempotentComplete :
    IsIdempotentComplete (SupportedSequenceRankQuotient (s := s) z) :=
  verdier_isIdempotentComplete _ _
    (fun _ _ f hf ↦ supportedRank_truncLE_denominator z K hK hKf hKn d hKb hfg hfin f hf)
    (supportedSequenceTStructure_bounded z K hK hKf hKn d hKb hfg hfin)

include hK hKf hKn hKb hfg hfin in
/-- 支持つきランク商の冪等完備化の対象は、商の前の支持つき自由列で表せる。 -/
theorem supportedRankKaroubi_has_representative
    (Y : Karoubi (SupportedSequenceRankQuotient (s := s) z)) :
    ∃ X : (supportedSequence (s := s) z).FullSubcategory,
      Nonempty ((toKaroubi _).obj
        ((rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q.obj X) ≅ Y) :=
  verdierKaroubi_has_representative _ _
    (fun _ _ f hf ↦ supportedRank_truncLE_denominator z K hK hKf hKn d hKb hfg hfin f hf)
    (supportedSequenceTStructure_bounded z K hK hKf hKn d hKb hfg hfin) Y

end SerrePositivity.Asymptotic
