module

public import SerrePositivity.Asymptotic.PaperRankQuotient
public import SerrePositivity.CategoryTheory.BoundedHomotopyGeneration

/-! # 論文の零部分圏を生成する次数零の小さい自由列 -/

@[expose] public section

universe u

set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.Limits Asymptotics Filter
open scoped ZeroObject

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ}

/-- 通常の o(s) 条件を満たす自由列。 -/
def rankSmallFree : ObjectProperty (FreeSequence R s) :=
  fun X ↦ (fun n ↦ (X.rank n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ))

instance : (rankSmallFree (R := R) (s := s)).IsClosedUnderIsomorphisms where
  of_iso i h := by
    dsimp only [rankSmallFree] at h ⊢
    simpa only [FreeSequence.rank_eq_of_iso i] using h

instance : (rankSmallFree (R := R) (s := s)).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, by
    change (fun n ↦ (((0 : FreeSequence R s).rank n : ℕ) : ℝ)) =o[atTop] _
    simpa only [FreeSequence.rank_eq_zero_of_isZero _ (isZero_zero _), Nat.cast_zero] using
      isLittleO_zero (fun n ↦ (s n : ℝ)) atTop⟩

/-- 論文の N_S の生成元：小さい自由列を次数零の単一複体として D_S に入れる。 -/
def paperSmallFreeGenerators : ObjectProperty (PaperSequenceCategory R s) :=
  fun Y ↦ ∃ X : FreeSequence R s, rankSmallFree X ∧
    Nonempty ((toKaroubi _).obj (boundedSingleObj X 0) ≅ Y)

instance : (paperSmallFreeGenerators (R := R) (s := s)).Nonempty :=
  ObjectProperty.nonempty_of_prop (X := (toKaroubi _).obj
    (boundedSingleObj (0 : FreeSequence R s) 0))
    ⟨0, rankSmallFree.prop_of_isZero (isZero_zero _), ⟨Iso.refl _⟩⟩

lemma rankSmallBounded_single (X : FreeSequence R s) (hX : rankSmallFree X) (a : ℤ) :
    rankSmallBounded (boundedSingleObj X a) := by
  let K := (HomologicalComplex.single (FreeSequence R s) (.up ℤ) a).obj X
  have hK : rankSmallComplex K := by
    refine ⟨strictlyBoundedComplex_single X a, fun i ↦ ?_⟩
    dsimp only [K]
    dsimp only [rankSmallFree] at hX
    by_cases hi : i = a
    · subst i
      simpa only [FreeSequence.rank_eq_of_iso (HomologicalComplex.singleObjXSelf (.up ℤ) a X)]
        using hX
    · simp only [FreeSequence.rank_eq_zero_of_isZero _
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) a X i hi), Nat.cast_zero]
      exact isLittleO_zero _ _
  exact ⟨_, (rankSmallHomotopy_quotient K).mpr hK, ⟨Iso.refl _⟩⟩

/-- 複体による実装の零部分圏は、論文の小さい自由列が生成する厚い部分圏と一致。 -/
theorem paperRankNull_eq_smallFreeEnvelope :
    paperRankNull R s = (paperSmallFreeGenerators (R := R) (s := s)).triangEnvelope := by
  let G := paperSmallFreeGenerators (R := R) (s := s)
  let Q := G.triangEnvelope.inverseImage (toKaroubi (SequenceHomotopy R s))
  apply le_antisymm
  · refine ((rankSmallBounded.map (toKaroubi (SequenceHomotopy R s))).triangEnvelope_le_iff).mpr ?_
    rintro Y ⟨X, hX, ⟨i⟩⟩
    apply G.triangEnvelope.prop_of_iso i
    obtain ⟨Z, hZ, ⟨j⟩⟩ := hX
    obtain ⟨K, hK⟩ := hZ
    let hB := hK.1
    have hq : Q (boundedComplexObj K hB) := by
      apply boundedHomotopy_mem_of_terms Q rankSmallFree _ K hB hK.2
      intro M hM a
      apply Q.prop_of_iso (boundedSingleShiftIso M a)
      apply (Q.prop_shift_iff_of_isStableUnderShift (boundedSingleObj M 0) (-a)).mpr
      exact G.le_triangEnvelope _ ⟨M, hM, ⟨Iso.refl _⟩⟩
    exact Q.prop_of_iso (ObjectProperty.isoMk _ j.symm) hq
  · refine (G.triangEnvelope_le_iff).mpr ?_
    rintro Y ⟨X, hX, ⟨i⟩⟩
    exact (paperRankNull R s).prop_of_iso i
      ((rankSmallBounded.map (toKaroubi (SequenceHomotopy R s))).le_triangEnvelope _
        (rankSmallBounded.prop_map_obj _ (rankSmallBounded_single X hX 0)))

end SerrePositivity.Asymptotic
