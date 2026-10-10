module

public import SerrePositivity.Asymptotic.LengthSerreQuotient

/-!
# 通常の o(s) の長さをもつ加群列の Serre 商

`atTop` における小さい長さの条件を使う。超極限零より強い条件であり、
自由列のランク商と比較する際はこちらを使う。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter Asymptotics
open scoped ZeroObject

variable {R : Type u} [CommRing R] {J : Ideal R}
  (lam : NormalizedLength R J) (s : ℕ → ℕ)

/-- 各段の長さが通常の `o(s)` になる条件。 -/
def smallSequenceLength : ObjectProperty (LengthBoundedSequence lam s) := fun M ↦
  (fun n : ℕ ↦ (lam.len (M.obj.obj ⟨n⟩)).toReal) =o[atTop] (fun n ↦ (s n : ℝ))

instance : (smallSequenceLength lam s).IsSerreClass where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    have hz (n : ℕ) : lam.len ((0 : LengthBoundedSequence lam s).obj.obj ⟨n⟩) = 0 := by
      have : Subsingleton ((0 : LengthBoundedSequence lam s).obj.obj ⟨n⟩) :=
        ModuleCat.isZero_iff_subsingleton.mp
          ((lengthSequenceEvaluation lam s n).map_isZero (isZero_zero _))
      exact lam.len_eq_zero_of_subsingleton _
    change (fun n : ℕ ↦ (lam.len ((0 : LengthBoundedSequence lam s).obj.obj ⟨n⟩)).toReal)
      =o[atTop] (fun n ↦ (s n : ℝ))
    simp_rw [hz, ENNReal.toReal_zero]
    exact isLittleO_zero _ _
  prop_of_mono {M N} f _ hN := by
    apply (isBigO_of_nonneg_le (fun _ ↦ ENNReal.toReal_nonneg) ?_).trans_isLittleO hN
    intro n
    apply ENNReal.toReal_mono (N.property.2.1 n)
    exact lam.len_le_of_injective ((lengthSequenceEvaluation lam s n).map f).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
      (uniformlyPowTorsion_apply N.property.1 n)
  prop_of_epi {M N} f _ hM := by
    apply (isBigO_of_nonneg_le (fun _ ↦ ENNReal.toReal_nonneg) ?_).trans_isLittleO hM
    intro n
    apply ENNReal.toReal_mono (M.property.2.1 n)
    exact lam.len_le_of_surjective ((lengthSequenceEvaluation lam s n).map f).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
      (uniformlyPowTorsion_apply M.property.1 n)
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have := hS.mono_f
    have := hS.epi_g
    have h := moduleSequence_length_add lam
      (hS.map (lengthBoundedSequence lam s).ι) S.X₂.property.1
    change ∀ n : ℕ, lam.len (S.X₂.obj.obj ⟨n⟩) =
      lam.len (S.X₁.obj.obj ⟨n⟩) + lam.len (S.X₃.obj.obj ⟨n⟩) at h
    change (fun n : ℕ ↦ (lam.len (S.X₂.obj.obj ⟨n⟩)).toReal) =o[atTop] _
    simp_rw [h, ENNReal.toReal_add (S.X₁.property.2.1 _) (S.X₃.property.2.1 _)]
    exact h₁.add h₃

/-- 通常の小さい長さによる Serre 商。 -/
abbrev SmallLengthSerreQuotient := (smallSequenceLength lam s).isoModSerre.Localization

noncomputable instance smallLengthSerreQuotientAbelian :
    Abelian (SmallLengthSerreQuotient lam s) := serreQuotientAbelian _

/-- 通常の小さい長さを消す完全関手。 -/
noncomputable abbrev smallLengthSerreQuotientFunctor :
    LengthBoundedSequence lam s ⥤ SmallLengthSerreQuotient lam s :=
  (smallSequenceLength lam s).isoModSerre.Q

noncomputable instance smallLengthSerreQuotientFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (smallLengthSerreQuotientFunctor lam s) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteLimits _ (smallSequenceLength lam s)

noncomputable instance smallLengthSerreQuotientFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (smallLengthSerreQuotientFunctor lam s) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteColimits _ (smallSequenceLength lam s)

/-- 小さい長さは、任意の非単項超フィルターによる長さ零を導く。 -/
lemma smallSequenceLength_le_zeroSequenceLength (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) : smallSequenceLength lam s ≤ zeroSequenceLength lam s U :=
  fun _ h ↦ normalizedLimit_eq_zero_of_isLittleO U hU s _ h

variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 超極限の長さの商関手は、通常の小さい長さの Serre 分母を可逆にする。 -/
lemma smallLength_inverted_by_lengthQuotient :
    (smallSequenceLength lam s).isoModSerre.IsInvertedBy
      (lengthSerreQuotientFunctor lam s U hU hs) :=
  ((smallSequenceLength lam s).isoModSerre_isInvertedBy_iff _).2
    (fun M hM ↦ (lengthSerreQuotient_isZero_iff lam s U hU hs M).2
      (smallSequenceLength_le_zeroSequenceLength lam s U hU M hM))

/-- 通常の小さい長さによる商から、超極限の長さ零による商への比較関手。 -/
noncomputable def smallLengthToLengthQuotient :
    SmallLengthSerreQuotient lam s ⥤ LengthSerreQuotient lam s U hU hs :=
  Localization.lift (lengthSerreQuotientFunctor lam s U hU hs)
    (smallLength_inverted_by_lengthQuotient lam s U hU hs) (smallLengthSerreQuotientFunctor lam s)

/-- 比較関手と二つの商関手の自然同型。 -/
noncomputable def smallLengthToLengthQuotientFactors :
    smallLengthSerreQuotientFunctor lam s ⋙ smallLengthToLengthQuotient lam s U hU hs ≅
      lengthSerreQuotientFunctor lam s U hU hs :=
  Localization.fac _ (smallLength_inverted_by_lengthQuotient lam s U hU hs) _

noncomputable instance smallLengthToLengthQuotient_preservesFiniteLimits :
    PreservesFiniteLimits (smallLengthToLengthQuotient lam s U hU hs) := by
  have := preservesFiniteLimits_of_natIso (smallLengthToLengthQuotientFactors lam s U hU hs).symm
  exact (ObjectProperty.SerreClassLocalization.preservesFiniteLimits_comp_iff
    (smallLengthSerreQuotientFunctor lam s) (smallSequenceLength lam s) _).1 inferInstance

noncomputable instance smallLengthToLengthQuotient_preservesFiniteColimits :
    PreservesFiniteColimits (smallLengthToLengthQuotient lam s U hU hs) := by
  have := preservesFiniteColimits_of_natIso (smallLengthToLengthQuotientFactors lam s U hU hs).symm
  exact (ObjectProperty.SerreClassLocalization.preservesFiniteColimits_comp_iff
    (smallLengthSerreQuotientFunctor lam s) (smallSequenceLength lam s) _).1 inferInstance

instance smallLengthToLengthQuotient_additive :
    (smallLengthToLengthQuotient lam s U hU hs).Additive :=
  Functor.additive_of_preserves_binary_products _

end SerrePositivity.Asymptotic
