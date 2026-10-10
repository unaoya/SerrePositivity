module

public import SerrePositivity.Asymptotic.RankSmallHomologyCriterion
public import SerrePositivity.CategoryTheory.FamilyTStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# 支持つき自由列の圏の有界 t 構造

各段の導来ホモロジーで次数条件を定める。
切り詰めの存在は、一様自由持ち上げと導来評価の完全忠実性から証明する。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated IsLocalRing

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
/-- 成分ごとの導来評価は、支持つき自由列の射の等式を検出する。 -/
lemma supportedDerivedEvaluation_jointly_faithful
    {X Y : (supportedSequence (s := s) z).FullSubcategory} (f g : X ⟶ Y)
    (h : ∀ n, (supportedDerivedEvaluation z n).map f = (supportedDerivedEvaluation z n).map g) :
    f = g := by
  apply (supportedSequence z).ι.map_injective
  apply pointwiseDerived.map_injective
  exact funext h

include hK hKf hKn hKb hfg hfin in
/-- 標準切り詰め三角形の族の左端には、共通の支持つき自由代表がある。 -/
lemma supportedSequence_truncation_family
    (X : (supportedSequence (s := s) z).FullSubcategory) :
    ∃ T : ℕ → Triangle (DerivedCategory (ModuleCat.{u} A)),
      (∀ n, T n ∈ distTriang _) ∧
      (∀ n, DerivedCategory.TStructure.t.le 0 (T n).obj₁) ∧
      (∀ n, DerivedCategory.TStructure.t.ge 1 (T n).obj₃) ∧
      (∀ n, Nonempty ((T n).obj₂ ≅ (supportedDerivedEvaluation z n).obj X)) ∧
      supportedDerivedImage (s := s) z (fun n ↦ (T n).obj₁) := by
  obtain ⟨⟨Y, hY⟩, hzY⟩ := X
  obtain ⟨P, rfl⟩ := Y.quotient_obj_surjective
  have hP := (boundedHomotopyProperty_quotient _ P).1 hY
  let L := fun n ↦ (evaluateComplex n).obj P
  obtain ⟨a, b, hbound⟩ := evaluateComplex_uniform_bounds P hP
  have ha (n : ℕ) : (L n).IsStrictlyGE a := (hbound n).1
  have hH (q : ℤ) : lengthBoundedSequence
      (ordinaryLengthOnIdeal (Ideal.span (Set.range z))) s (familyHomology L q) := by
    exact (lengthBoundedSequence _ s).prop_of_iso (sequenceHomologyComplexIso P hP q)
      (sequenceHomology_lengthBounded _ hfg z Ideal.le_radical hfin
        (sequenceHomotopyObj P hP) hzY q)
  refine ⟨fun n ↦ DerivedCategory.triangleOfSES ((L n).shortComplexTruncLE_shortExact 0),
    fun n ↦ DerivedCategory.triangleOfSES_distinguished _, fun n ↦ ?_, fun n ↦ ?_,
    fun n ↦ ⟨(supportedDerivedEvaluation_complexIso z P hP hzY n).symm⟩, ?_⟩
  · change DerivedCategory.TStructure.t.le 0 (DerivedCategory.Q.obj ((L n).truncLE 0))
    exact DerivedCategory.TStructure.t.le_of_isLE _ 0
  · let i := asIso (DerivedCategory.Q.map ((L n).shortComplexTruncLEX₃ToTruncGE 0 1 rfl))
    exact (DerivedCategory.TStructure.t.ge 1).prop_of_iso i.symm
      (DerivedCategory.TStructure.t.ge_of_isGE _ 1)
  · apply supportedDerivedImage_of_uniform_bounds z K hK hKf hKn d hKb
      (fun n ↦ DerivedCategory.Q.obj ((L n).truncLE 0)) a 0
      (fun n ↦ inferInstance) (fun n ↦ inferInstance)
    intro q
    exact (lengthBoundedSequence _ s).prop_of_iso
      (familyDerivedHomologyIso (fun n ↦ (L n).truncLE 0) q).symm
      (familyHomology_truncLE_prop L _ hH 0 q)

/-- 支持つき自由列上の、成分ごとのホモロジーで定まる t 構造。 -/
noncomputable def supportedSequenceTStructure :
    TStructure (supportedSequence (s := s) z).FullSubcategory :=
  familyTStructure (supportedDerivedEvaluation z) DerivedCategory.TStructure.t
    (supportedDerivedEvaluation_full z) (supportedDerivedEvaluation_jointly_faithful z)
    (supportedSequence_truncation_family z K hK hKf hKn d hKb hfg hfin)

/-- 各段の導来評価は t 完全である。 -/
lemma supportedSequenceTStructure_evaluation_tExact (n : ℕ) :
    (supportedDerivedEvaluation (s := s) z n).TExact
      (supportedSequenceTStructure z K hK hKf hKn d hKb hfg hfin) DerivedCategory.TStructure.t :=
  familyTStructure_tExact _ _ _ _ _ n

/-- 共通の次数範囲により、この t 構造は有界である。 -/
lemma supportedSequenceTStructure_bounded
    (X : (supportedSequence (s := s) z).FullSubcategory) :
    (supportedSequenceTStructure z K hK hKf hKn d hKb hfg hfin).bounded X := by
  obtain ⟨a, b, hb⟩ := supportedDerivedEvaluation_uniform_bounds z X
  exact ⟨⟨a, ⟨fun n ↦ (hb n).1.ge⟩⟩, ⟨b, ⟨fun n ↦ (hb n).2.le⟩⟩⟩

end SerrePositivity.Asymptotic
