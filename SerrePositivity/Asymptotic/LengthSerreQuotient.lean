module

public import SerrePositivity.Asymptotic.LengthBoundedSequence
public import SerrePositivity.CategoryTheory.AdditiveLength

/-!
# 正規化超極限が零の加群列による Serre 商

長さが `O(s)` の一様冪ねじれ加群列の圏に、実数値の正規化超極限を定義する。
非負性・短完全列に対する加法性から、零評価の対象が Serre 部分圏をなす。
この部分圏による局所化を実際のアーベル商圏として構成する。
支持つき Verdier 商からこの圏へのホモロジー評価は別の構成である。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter Asymptotics
open scoped ZeroObject

variable {R : Type u} [CommRing R] {J : Ideal R}
  (lam : NormalizedLength R J) (s : ℕ → ℕ)

/-- 長さで制限した加群列の各段への完全関手。 -/
abbrev lengthSequenceEvaluation (n : ℕ) : LengthBoundedSequence lam s ⥤ ModuleCat.{u} R :=
  (lengthBoundedSequence lam s).ι ⋙ moduleSequenceEvaluation n

/-- 長さで制限した加群列の正規化超極限。 -/
noncomputable def sequenceLength (U : Ultrafilter ℕ) (M : LengthBoundedSequence lam s) : ℝ :=
  normalizedLimit U s (fun n ↦ (lam.len (M.obj.obj ⟨n⟩)).toReal)

variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

include hU hs in
/-- 正規化超極限としての長さは非負である。 -/
lemma sequenceLength_nonneg (M : LengthBoundedSequence lam s) :
    0 ≤ sequenceLength lam s U M :=
  normalizedLimit_nonneg U hU s hs _ M.property.2.2
    (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)

/-- 零対象の長さは零である。 -/
lemma sequenceLength_of_isZero (M : LengthBoundedSequence lam s) (hM : IsZero M) :
    sequenceLength lam s U M = 0 := by
  have h (n : ℕ) : lam.len (M.obj.obj ⟨n⟩) = 0 := by
    have : Subsingleton (M.obj.obj ⟨n⟩) :=
      ModuleCat.isZero_iff_subsingleton.mp ((lengthSequenceEvaluation lam s n).map_isZero hM)
    exact lam.len_eq_zero_of_subsingleton _
  simp [sequenceLength, h]

/-- 加群列の同型は各段の長さを保つため、正規化超極限も保つ。 -/
lemma sequenceLength_iso {M N : LengthBoundedSequence lam s} (e : M ≅ N) :
    sequenceLength lam s U M = sequenceLength lam s U N := by
  have h (n : ℕ) : lam.len (M.obj.obj ⟨n⟩) = lam.len (N.obj.obj ⟨n⟩) :=
    lam.len_congr _ _ ((lengthSequenceEvaluation lam s n).mapIso e).toLinearEquiv
  simp only [sequenceLength, h]

include hU hs in
/-- 単射に沿って長さは増加する。 -/
lemma sequenceLength_le_of_mono {M N : LengthBoundedSequence lam s} (f : M ⟶ N) [Mono f] :
    sequenceLength lam s U M ≤ sequenceLength lam s U N := by
  apply le_of_tendsto_of_tendsto'
    (normalizedLimit_tendsto U hU s hs _ M.property.2.2)
    (normalizedLimit_tendsto U hU s hs _ N.property.2.2)
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply ENNReal.toReal_mono (N.property.2.1 n)
  exact lam.len_le_of_injective ((lengthSequenceEvaluation lam s n).map f).hom
    ((ModuleCat.mono_iff_injective _).1 inferInstance)
    (uniformlyPowTorsion_apply N.property.1 n)

include hU hs in
/-- 全射に沿って長さは減少する。 -/
lemma sequenceLength_le_of_epi {M N : LengthBoundedSequence lam s} (f : M ⟶ N) [Epi f] :
    sequenceLength lam s U N ≤ sequenceLength lam s U M := by
  apply le_of_tendsto_of_tendsto'
    (normalizedLimit_tendsto U hU s hs _ N.property.2.2)
    (normalizedLimit_tendsto U hU s hs _ M.property.2.2)
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply ENNReal.toReal_mono (M.property.2.1 n)
  exact lam.len_le_of_surjective ((lengthSequenceEvaluation lam s n).map f).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    (uniformlyPowTorsion_apply M.property.1 n)

include hU hs in
/-- 長さの正規化超極限は短完全列に対して加法的である。 -/
lemma sequenceLength_add {S : ShortComplex (LengthBoundedSequence lam s)}
    (hS : S.ShortExact) :
    sequenceLength lam s U S.X₂ = sequenceLength lam s U S.X₁ + sequenceLength lam s U S.X₃ := by
  have := hS.mono_f
  have := hS.epi_g
  have h := moduleSequence_length_add lam
    (hS.map (lengthBoundedSequence lam s).ι) S.X₂.property.1
  change ∀ n : ℕ, lam.len (S.X₂.obj.obj ⟨n⟩) =
    lam.len (S.X₁.obj.obj ⟨n⟩) + lam.len (S.X₃.obj.obj ⟨n⟩) at h
  dsimp only [sequenceLength]
  simp_rw [h, ENNReal.toReal_add (S.X₁.property.2.1 _) (S.X₃.property.2.1 _)]
  exact normalizedLimit_add U hU s hs _ _ S.X₁.property.2.2 S.X₃.property.2.2

/-- 正規化超極限としての長さが零となる対象の条件。 -/
def zeroSequenceLength : ObjectProperty (LengthBoundedSequence lam s) :=
  fun M ↦ sequenceLength lam s U M = 0

include hU hs in
/-- 非負加法的な長さの零対象は Serre 部分圏をなす。 -/
lemma zeroSequenceLength_isSerreClass : (zeroSequenceLength lam s U).IsSerreClass :=
  zeroAdditiveLength_isSerreClass (sequenceLength lam s U)
    (sequenceLength_add lam s U hU hs) (sequenceLength_nonneg lam s U hU hs)
    (sequenceLength_of_isZero lam s U _ (isZero_zero _))

/-- 零長さの対象で割った加群列の Serre 商。 -/
abbrev LengthSerreQuotient :=
  haveI := zeroSequenceLength_isSerreClass lam s U hU hs
  (zeroSequenceLength lam s U).isoModSerre.Localization

/-- 長さの Serre 商はアーベル圏である。 -/
noncomputable instance lengthSerreQuotientAbelian :
    Abelian (LengthSerreQuotient lam s U hU hs) := by
  letI := zeroSequenceLength_isSerreClass lam s U hU hs
  exact serreQuotientAbelian _

/-- 長さの Serre 商への標準関手。 -/
noncomputable abbrev lengthSerreQuotientFunctor :
    LengthBoundedSequence lam s ⥤ LengthSerreQuotient lam s U hU hs :=
  haveI := zeroSequenceLength_isSerreClass lam s U hU hs
  (zeroSequenceLength lam s U).isoModSerre.Q

/-- 商で零になる対象は正規化超極限が零の対象に一致する。 -/
lemma lengthSerreQuotient_isZero_iff (M : LengthBoundedSequence lam s) :
    IsZero ((lengthSerreQuotientFunctor lam s U hU hs).obj M) ↔
      sequenceLength lam s U M = 0 := by
  let := zeroSequenceLength_isSerreClass lam s U hU hs
  exact ObjectProperty.SerreClassLocalization.isZero_obj_iff
    (lengthSerreQuotientFunctor lam s U hU hs) (zeroSequenceLength lam s U) M

/-- Serre 商関手は加法的である。 -/
instance lengthSerreQuotientFunctor_additive :
    (lengthSerreQuotientFunctor lam s U hU hs).Additive := by
  let := zeroSequenceLength_isSerreClass lam s U hU hs
  infer_instance

/-- Serre 商関手は有限極限を保つ。 -/
noncomputable instance lengthSerreQuotientFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (lengthSerreQuotientFunctor lam s U hU hs) := by
  let := zeroSequenceLength_isSerreClass lam s U hU hs
  exact ObjectProperty.SerreClassLocalization.preservesFiniteLimits
    (lengthSerreQuotientFunctor lam s U hU hs) (zeroSequenceLength lam s U)

/-- Serre 商関手は有限余極限を保つ。 -/
noncomputable instance lengthSerreQuotientFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (lengthSerreQuotientFunctor lam s U hU hs) := by
  let := zeroSequenceLength_isSerreClass lam s U hU hs
  exact ObjectProperty.SerreClassLocalization.preservesFiniteColimits
    (lengthSerreQuotientFunctor lam s U hU hs) (zeroSequenceLength lam s U)

end SerrePositivity.Asymptotic
