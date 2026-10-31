module

public import SerrePositivity.Asymptotic.CompletedComplexEvaluation
public import SerrePositivity.Asymptotic.SequenceBaseChangeSupport
public import SerrePositivity.CategoryTheory.ScalarSupport

/-! # 商の完備化上の係数変更と支持 -/

@[expose] public section

universe u

set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents

variable {R S : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} (φ : R →+* S)

omit [Nontrivial R] [Nontrivial S] in
lemma sequenceChangeRing_map_smul_id (X : SequenceHomotopy R s) (r : R) :
    (mapBoundedHomotopy (FreeSequence.changeRing φ)).map (r • 𝟙 X) =
      φ r • 𝟙 ((mapBoundedHomotopy (FreeSequence.changeRing φ)).obj X) := by
  obtain ⟨Y, hY⟩ := X
  obtain ⟨K, rfl⟩ := Y.quotient_obj_surjective
  apply ObjectProperty.hom_ext
  change ((FreeSequence.changeRing φ).mapHomotopyCategory (.up ℤ)).map
    (r • 𝟙 ((HomotopyCategory.quotient _ _).obj K)) = _
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul]
  change (HomotopyCategory.quotient _ _).map
    (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).map (r • 𝟙 K)) = _
  rw [changeRing_complex_map_smul, CategoryTheory.Functor.map_id,
    Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

lemma rankQuotientChangeRing_map_smul_id (X : SequenceRankQuotient R s) (r : R) :
    (rankQuotientChangeRing φ).map (r • 𝟙 X) =
      φ r • 𝟙 ((rankQuotientChangeRing φ).obj X) := by
  apply map_smul_id_of_precomp φ sequenceRankQuotientFunctor (rankQuotientChangeRing φ)
    _ (rankQuotientChangeRing_fac φ) _ X r
  intro Y a
  simp only [Functor.comp_obj, Functor.comp_map, sequenceChangeRing_map_smul_id, Functor.map_smul,
    CategoryTheory.Functor.map_id]

/-- 全体のランク商の完備化上の標準的な係数変更。 -/
noncomputable abbrev completedChangeRing :
    CompletedSequenceRankQuotient R s ⥤ CompletedSequenceRankQuotient S s :=
  (functorExtension₂ _ _).obj (rankQuotientChangeRing φ)

lemma completedChangeRing_map_smul_id (X : CompletedSequenceRankQuotient R s) (r : R) :
    (completedChangeRing φ).map (r • 𝟙 X) =
      φ r • 𝟙 ((completedChangeRing φ).obj X) := by
  have h : (rankQuotientChangeRing φ).map (r • X.p) =
      φ r • (rankQuotientChangeRing φ).map X.p := by
    calc
      _ = (rankQuotientChangeRing φ).map (X.p ≫ (r • 𝟙 X.X)) := by simp
      _ = _ := by rw [Functor.map_comp, rankQuotientChangeRing_map_smul_id]; simp
  exact Karoubi.hom_ext _ _ h

/-- 商の完備化で初めて現れる支持も係数変更で保たれる。 -/
lemma completedChangeRing_supported {e : ℕ} (z : Fin e → R)
    (X : CompletedSequenceRankQuotient R s) (hX : scalarSupported z X) :
    scalarSupported (φ ∘ z) ((completedChangeRing φ).obj X) := by
  obtain ⟨v, hv, h⟩ := hX
  refine ⟨v, hv, fun j ↦ ?_⟩
  have hj := (completedChangeRing φ).congr_map (h j)
  simpa only [Function.comp_apply, completedChangeRing_map_smul_id, map_pow,
    Functor.map_zero] using hj

/-- 共通有界複体列からの像と係数変更の可換性。 -/
noncomputable def completedChangeRingFactors :
    completedSequenceFunctor (R := R) (s := s) ⋙ completedChangeRing φ ≅
      mapBoundedHomotopy (FreeSequence.changeRing φ) ⋙ completedSequenceFunctor :=
  isoWhiskerLeft sequenceRankQuotientFunctor
    ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app (rankQuotientChangeRing φ)) ≪≫
    isoWhiskerRight (rankQuotientChangeRing_fac φ) (toKaroubi _)

end SerrePositivity.Asymptotic
