module

public import SerrePositivity.Asymptotic.SupportedRankTStructure
public import SerrePositivity.Asymptotic.SupportedKaroubi

/-!
# 冪等完備化後の支持対象の一様自由代表

支持つきランク商の冪等完備性と、既存の支持部分圏の比較を組み合わせる。
商を取った後・冪等完備化した後に台をもつ対象にも、
商の前に一様に台をもつ実際の自由複体列の代表を選べる。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents IsLocalRing

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

include hK hKf hKn hKb hfg hfin in
/-- 全体のランク商の冪等完備化で台をもつ対象に、支持つきの代表がある。 -/
theorem supportedCompleted_has_representative
    (Y : CompletedSequenceRankQuotient A s) (hY : supportedCompletedRankQuotient z Y) :
    ∃ X : (supportedSequence (s := s) z).FullSubcategory,
      Nonempty ((toKaroubi _).obj (sequenceRankQuotientFunctor.obj X.obj) ≅ Y) := by
  let B := rankSmallBounded (R := A) (s := s)
  let S := supportedSequence (s := s) z
  let L := (B.inverseImage S.ι).trW.Q
  let F := supportedRankQuotientInclusion (s := s) z
  let E := (functorExtension₂ _ _).obj F
  obtain ⟨Y', ⟨iY⟩⟩ := supportedKaroubi_mem_essImage z Y hY
  obtain ⟨X, ⟨iX⟩⟩ := supportedRankKaroubi_has_representative
    z K hK hKf hKn d hKb hfg hfin Y'
  let Φ := S.triangulatedLocalizerMorphism B
  let i : sequenceRankQuotientFunctor.obj X.obj ≅ F.obj (L.obj X) :=
    (CatCommSq.iso Φ.functor L B.trW.Q (Φ.localizedFunctor L B.trW.Q)).app X
  exact ⟨X, ⟨(toKaroubi _).mapIso i ≪≫
    (((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app F).app (L.obj X)).symm ≪≫
      E.mapIso iX ≪≫ iY⟩⟩

include hK hKf hKn hKb hfg hfin in
/-- 冪等完備化後の任意の支持対象には、共通有界な支持つき自由複体列の代表がある。 -/
theorem supportedCompleted_has_complex_representative
    (Y : CompletedSequenceRankQuotient A s) (hY : supportedCompletedRankQuotient z Y) :
    ∃ (P : CochainComplex (FreeSequence A s) ℤ)
      (hP : strictlyBoundedComplex (FreeSequence A s) P),
      supportedSequence z (sequenceHomotopyObj P hP) ∧
      Nonempty ((toKaroubi _).obj
        (sequenceRankQuotientFunctor.obj (sequenceHomotopyObj P hP)) ≅ Y) := by
  obtain ⟨⟨⟨X, hX⟩, hzX⟩, ⟨iX⟩⟩ :=
    supportedCompleted_has_representative z K hK hKf hKn d hKb hfg hfin Y hY
  obtain ⟨P, rfl⟩ := X.quotient_obj_surjective
  have hP := (boundedHomotopyProperty_quotient _ P).1 hX
  exact ⟨P, hP, hzX, ⟨iX⟩⟩

end SerrePositivity.Asymptotic
