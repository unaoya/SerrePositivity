module

public import SerrePositivity.Asymptotic.ModuleSequence
public import SerrePositivity.Asymptotic.LengthFamilies
public import SerrePositivity.CategoryTheory.SerreSubcategory

/-!
# 長さが一様に制御された加群列のアーベル圏

共通のイデアル冪で消え、各段の正規化長さが有限で、長さの列が `O(s)` となる
加群列を扱う。有限性を実数化より先に要求する。この条件が Serre 条件を満たすことを
証明し、充満部分圏にアーベル圏構造を与える。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter Asymptotics
open scoped ZeroObject

variable {R : Type u} [CommRing R] {J : Ideal R}

/-- 加群列の短完全列は各段でも短完全である。 -/
lemma moduleSequence_shortExact_eval {S : ShortComplex (ModuleSequence R)}
    (hS : S.ShortExact) (n : ℕ) :
    (S.map (moduleSequenceEvaluation n)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map (moduleSequenceEvaluation n)

variable (lam : NormalizedLength R J) (s : ℕ → ℕ)

/-- 共通の冪で消え、各段で有限長、長さの列が `O(s)` であるという条件。 -/
def lengthBoundedSequence : ObjectProperty (ModuleSequence R) := fun M ↦
  uniformlyPowTorsion J M ∧ (∀ n : ℕ, lam.len (M.obj ⟨n⟩) ≠ ⊤) ∧
    (fun n : ℕ ↦ (lam.len (M.obj ⟨n⟩)).toReal) =O[atTop] (fun n ↦ (s n : ℝ))

instance : (lengthBoundedSequence lam s).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, (uniformlyPowTorsion J).prop_zero, ?_, ?_⟩
    · intro n
      have : Subsingleton ((0 : ModuleSequence R).obj ⟨n⟩) :=
        ModuleCat.isZero_iff_subsingleton.mp
          ((moduleSequenceEvaluation n).map_isZero (isZero_zero _))
      rw [lam.len_eq_zero_of_subsingleton]
      exact ENNReal.zero_ne_top
    · have h : ∀ n : ℕ, lam.len ((0 : ModuleSequence R).obj ⟨n⟩) = 0 := by
        intro n
        have : Subsingleton ((0 : ModuleSequence R).obj ⟨n⟩) :=
          ModuleCat.isZero_iff_subsingleton.mp
            ((moduleSequenceEvaluation n).map_isZero (isZero_zero _))
        exact lam.len_eq_zero_of_subsingleton _
      simp_rw [h, ENNReal.toReal_zero]
      exact isBigO_zero _ _

instance : (lengthBoundedSequence lam s).IsClosedUnderSubobjects where
  prop_of_mono {M N} f _ hN := by
    have hle (n : ℕ) : lam.len (M.obj ⟨n⟩) ≤ lam.len (N.obj ⟨n⟩) :=
      lam.len_le_of_injective (f.app ⟨n⟩).hom
        ((ModuleCat.mono_iff_injective _).1 inferInstance)
        (uniformlyPowTorsion_apply hN.1 n)
    exact ⟨(uniformlyPowTorsion J).prop_of_mono f hN.1,
      fun n ↦ ne_top_of_le_ne_top (hN.2.1 n) (hle n),
      (isBigO_of_nonneg_le (fun _ ↦ ENNReal.toReal_nonneg)
        (fun n ↦ ENNReal.toReal_mono (hN.2.1 n) (hle n))).trans hN.2.2⟩

instance : (lengthBoundedSequence lam s).IsClosedUnderQuotients where
  prop_of_epi {M N} f _ hM := by
    have hle (n : ℕ) : lam.len (N.obj ⟨n⟩) ≤ lam.len (M.obj ⟨n⟩) :=
      lam.len_le_of_surjective (f.app ⟨n⟩).hom
        ((ModuleCat.epi_iff_surjective _).1 inferInstance)
        (uniformlyPowTorsion_apply hM.1 n)
    exact ⟨(uniformlyPowTorsion J).prop_of_epi f hM.1,
      fun n ↦ ne_top_of_le_ne_top (hM.2.1 n) (hle n),
      (isBigO_of_nonneg_le (fun _ ↦ ENNReal.toReal_nonneg)
        (fun n ↦ ENNReal.toReal_mono (hM.2.1 n) (hle n))).trans hM.2.2⟩

/-- 共通の冪で消える短完全列では正規化長さが各段で加法的である。 -/
lemma moduleSequence_length_add {S : ShortComplex (ModuleSequence R)}
    (hS : S.ShortExact) (h₂ : uniformlyPowTorsion J S.X₂) (n : ℕ) :
    lam.len (S.X₂.obj ⟨n⟩) = lam.len (S.X₁.obj ⟨n⟩) + lam.len (S.X₃.obj ⟨n⟩) := by
  have hn := moduleSequence_shortExact_eval hS n
  exact lam.len_add_of_exact _ _ _ (S.f.app ⟨n⟩).hom (S.g.app ⟨n⟩).hom
    hn.moduleCat_injective_f hn.moduleCat_surjective_g
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S.map (moduleSequenceEvaluation n))).mp hn.exact)
    (uniformlyPowTorsion_apply h₂ n)

instance : (lengthBoundedSequence lam s).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have ht := (uniformlyPowTorsion J).prop_X₂_of_shortExact hS h₁.1 h₃.1
    have he := moduleSequence_length_add lam hS ht
    refine ⟨ht, fun n ↦ ?_, ?_⟩
    · rw [he n]
      exact ENNReal.add_ne_top.mpr ⟨h₁.2.1 n, h₃.2.1 n⟩
    · simp_rw [he, ENNReal.toReal_add (h₁.2.1 _) (h₃.2.1 _)]
      exact h₁.2.2.add h₃.2.2

instance : (lengthBoundedSequence lam s).IsSerreClass where

/-- 長さが `O(s)` の一様冪ねじれ加群列の圏。 -/
abbrev LengthBoundedSequence := (lengthBoundedSequence lam s).FullSubcategory

/-- 上の圏は Serre 部分圏としてアーベル圏になる。 -/
noncomputable example : Abelian (LengthBoundedSequence lam s) := inferInstance

end SerrePositivity.Asymptotic
