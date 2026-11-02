module

public import SerrePositivity.LengthAlgebra.Core
public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Category
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import SerrePositivity.Asymptotic.NormalizedLimit
public import SerrePositivity.CategoryTheory.Abelian.SerreLength
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import SerrePositivity.CategoryTheory.Derived

/-! # 長さが一様に制御された加群の列

## 概要

共通のイデアルの冪で消える加群の列（離散圏からの関手）と、正規化長さが有限で長さの列が O(s) となるもののアーベル圏を作り、正規化超極限が零の列による Serre 商と、その上の忠実な長さ（命題 4.3 の評価先）、通常の o(s) の長さによる Serre 商を与える。複体の族のホモロジーの切り詰めと、導来対象の族の有限 Postnikov 帰納法も与える。

## 方針

拡大では両端の指数の和が中央を消すので一様性が保たれる。有限性を実数化より先に要求する。

## 規約

`uniformlyPowTorsion` と Serre 類の instance は CommutativeAlgebra/PowerTorsion と同じ型の議論（一本化は保留）。FamilyPostnikov・FamilyHomologyTruncation は HomologicalAlgebra へ移す候補（refactor-plan §7.2）。

## 使われ方

`SequenceHomology`・`UniformLift`。
-/

@[expose] public noncomputable section

universe u

section ModuleSequencePart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

/-- 加群の列のアーベル圏。 -/
abbrev ModuleSequence (R : Type u) [CommRing R] := Discrete ℕ ⥤ ModuleCat.{u} R

variable {R : Type u} [CommRing R]

/-- 加群列の第 `n` 項への評価。 -/
abbrev moduleSequenceEvaluation (n : ℕ) : ModuleSequence R ⥤ ModuleCat.{u} R :=
  (CategoryTheory.evaluation _ _).obj ⟨n⟩

/-- 一つの指数で列のすべての加群を消す条件。 -/
def uniformlyPowTorsion (J : Ideal R) : ObjectProperty (ModuleSequence R) :=
  fun M ↦ ∃ k : ℕ, ∀ n : ℕ, J ^ k ≤ Module.annihilator R (M.obj ⟨n⟩)

/-- 一様な冪ねじれ性から、各段の長さを扱うための冪ねじれ性を得る。 -/
lemma uniformlyPowTorsion_apply {J : Ideal R} {M : ModuleSequence R}
    (hM : uniformlyPowTorsion J M) (n : ℕ) : IsPowTorsion J (M.obj ⟨n⟩) := by
  obtain ⟨k, hk⟩ := hM
  refine ⟨k, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe]
  exact hk n

variable (J : Ideal R)

instance : (uniformlyPowTorsion J).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, 0, fun n ↦ by
    have : Subsingleton ((0 : ModuleSequence R).obj ⟨n⟩) :=
      ModuleCat.isZero_iff_subsingleton.mp
        ((moduleSequenceEvaluation n).map_isZero (isZero_zero _))
    intro a _
    rw [Module.mem_annihilator]
    intro x
    exact Subsingleton.elim _ _⟩

instance : (uniformlyPowTorsion J).IsClosedUnderSubobjects where
  prop_of_mono {M N} f _ hN := by
    obtain ⟨k, hk⟩ := hN
    refine ⟨k, fun n ↦ (hk n).trans ?_⟩
    exact (f.app ⟨n⟩).hom.annihilator_le_of_injective
      ((ModuleCat.mono_iff_injective _).1 inferInstance)

instance : (uniformlyPowTorsion J).IsClosedUnderQuotients where
  prop_of_epi {M N} f _ hM := by
    obtain ⟨k, hk⟩ := hM
    refine ⟨k, fun n ↦ (hk n).trans ?_⟩
    exact (f.app ⟨n⟩).hom.annihilator_le_of_surjective
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)

instance : (uniformlyPowTorsion J).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    obtain ⟨a, ha⟩ := h₁
    obtain ⟨b, hb⟩ := h₃
    have := hS.mono_f
    have := hS.epi_g
    refine ⟨a + b, fun n ↦ ?_⟩
    exact annihilator_pow_add_of_exact J (S.map (moduleSequenceEvaluation n))
      (hS.map (moduleSequenceEvaluation n)).exact a b (ha n) (hb n)

instance : (uniformlyPowTorsion J).IsSerreClass where

end SerrePositivity.Asymptotic

end ModuleSequencePart

section LengthBoundedSequencePart

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

end LengthBoundedSequencePart

section LengthSerreQuotientPart

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

end LengthSerreQuotientPart

section LengthQuotientValuePart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter

variable {R : Type u} [CommRing R] {J : Ideal R}
  (lam : NormalizedLength R J) (s : ℕ → ℕ)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- Serre 商上の実数値の長さ。 -/
noncomputable def lengthQuotientValue (X : LengthSerreQuotient lam s U hU hs) : ℝ :=
  haveI := zeroSequenceLength_isSerreClass lam s U hU hs
  serreQuotientLength (zeroSequenceLength lam s U) (sequenceLength lam s U) X

/-- 元の加群列の像では正規化超極限に一致する。 -/
@[simp] lemma lengthQuotientValue_obj (M : LengthBoundedSequence lam s) :
    lengthQuotientValue lam s U hU hs ((lengthSerreQuotientFunctor lam s U hU hs).obj M) =
      sequenceLength lam s U M := rfl

/-- 商上の長さは非負である。 -/
lemma lengthQuotientValue_nonneg (X : LengthSerreQuotient lam s U hU hs) :
    0 ≤ lengthQuotientValue lam s U hU hs X :=
  sequenceLength_nonneg lam s U hU hs _

/-- 商で新しく現れる同型に対しても長さは不変である。 -/
lemma lengthQuotientValue_iso {X Y : LengthSerreQuotient lam s U hU hs} (e : X ≅ Y) :
    lengthQuotientValue lam s U hU hs X = lengthQuotientValue lam s U hU hs Y := by
  let := zeroSequenceLength_isSerreClass lam s U hU hs
  exact serreQuotientLength_iso (zeroSequenceLength lam s U) (sequenceLength lam s U)
    (sequenceLength_iso lam s U) (sequenceLength_add lam s U hU hs) (fun _ h ↦ h) e

/-- 商の任意の短完全列に対して長さは加法的である。 -/
lemma lengthQuotientValue_add {S : ShortComplex (LengthSerreQuotient lam s U hU hs)}
    (hS : S.ShortExact) :
    lengthQuotientValue lam s U hU hs S.X₂ = lengthQuotientValue lam s U hU hs S.X₁ +
      lengthQuotientValue lam s U hU hs S.X₃ := by
  let := zeroSequenceLength_isSerreClass lam s U hU hs
  exact serreQuotientLength_add (zeroSequenceLength lam s U) (sequenceLength lam s U)
    (sequenceLength_iso lam s U) (sequenceLength_add lam s U hU hs) (fun _ h ↦ h) hS

/-- 商上では、長さが零であることと零対象であることが一致する。 -/
lemma lengthQuotientValue_eq_zero_iff (X : LengthSerreQuotient lam s U hU hs) :
    lengthQuotientValue lam s U hU hs X = 0 ↔ IsZero X := by
  let := zeroSequenceLength_isSerreClass lam s U hU hs
  exact serreQuotientLength_eq_zero_iff (zeroSequenceLength lam s U)
    (sequenceLength lam s U) (fun _ ↦ Iff.rfl) X

end SerrePositivity.Asymptotic

end LengthQuotientValuePart

section SmallLengthSerreQuotientPart

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

end SmallLengthSerreQuotientPart

section FamilyHomologyTruncationPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {J : Ideal R}
  (lam : NormalizedLength R J) (s : ℕ → ℕ)
  (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)

/-- 複体の族の第 q ホモロジーを加群列とみなす。 -/
noncomputable abbrev familyHomology (q : ℤ) : ModuleSequence R :=
  Discrete.functor (fun n ↦ (K n).homology q)

/-- 全成分が零なら、ホモロジーの加群列も零。 -/
lemma familyHomology_isZero (q : ℤ) (h : ∀ n, IsZero ((K n).homology q)) :
    IsZero (familyHomology K q) := by
  rw [IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext n
  exact (h n.as).eq_of_src _ _

/-- 非正切り詰めは各次数の長さの一様条件を保つ。 -/
lemma familyHomology_truncLE_prop
    (Q : ObjectProperty (ModuleSequence R)) [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]
    (hK : ∀ q, Q (familyHomology K q)) (b q : ℤ) :
    Q (familyHomology (fun n ↦ (K n).truncLE b) q) := by
  by_cases hq : q ≤ b
  · have (n : ℕ) : QuasiIsoAt ((K n).ιTruncLE b) q := (K n).quasiIsoAt_ιTruncLE b q hq
    exact (Q).prop_of_iso
      (Discrete.natIso (fun n ↦ (isoOfQuasiIsoAt ((K n.as).ιTruncLE b) q).symm))
      (hK q)
  · apply (Q).prop_of_isZero
    exact familyHomology_isZero _ q (fun n ↦
      ((K n).truncLE b).exactAt_of_isLE b q (by omega) |>.isZero_homology)

/-- 非負切り詰めは各次数の長さの一様条件を保つ。 -/
lemma familyHomology_truncGE_prop
    (Q : ObjectProperty (ModuleSequence R)) [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]
    (hK : ∀ q, Q (familyHomology K q)) (a q : ℤ) :
    Q (familyHomology (fun n ↦ (K n).truncGE a) q) := by
  by_cases hq : a ≤ q
  · have (n : ℕ) : QuasiIsoAt ((K n).πTruncGE a) q := (K n).quasiIsoAt_πTruncGE a q hq
    exact (Q).prop_of_iso
      (Discrete.natIso (fun n ↦ isoOfQuasiIsoAt ((K n.as).πTruncGE a) q)) (hK q)
  · apply (Q).prop_of_isZero
    exact familyHomology_isZero _ q (fun n ↦
      ((K n).truncGE a).exactAt_of_isGE a q (by omega) |>.isZero_homology)

/-- 非正切り詰めは各次数の長さの一様条件を保つ。 -/
lemma familyHomology_truncLE_lengthBounded
    (hK : ∀ q, lengthBoundedSequence lam s (familyHomology K q)) (b q : ℤ) :
    lengthBoundedSequence lam s (familyHomology (fun n ↦ (K n).truncLE b) q) :=
  familyHomology_truncLE_prop K (lengthBoundedSequence lam s) hK b q

/-- 非負切り詰めは各次数の長さの一様条件を保つ。 -/
lemma familyHomology_truncGE_lengthBounded
    (hK : ∀ q, lengthBoundedSequence lam s (familyHomology K q)) (a q : ℤ) :
    lengthBoundedSequence lam s (familyHomology (fun n ↦ (K n).truncGE a) q) :=
  familyHomology_truncGE_prop K (lengthBoundedSequence lam s) hK a q

variable [HasDerivedCategory (ModuleCat.{u} R)]

/-- 複体の族とその導来像とのホモロジーの比較。 -/
noncomputable def familyDerivedHomologyIso (q : ℤ) :
    Discrete.functor (fun n ↦ (DerivedCategory.homologyFunctor (ModuleCat R) q).obj
      (DerivedCategory.Q.obj (K n))) ≅ familyHomology K q :=
  Discrete.natIso (fun n ↦ (DerivedCategory.homologyFunctorFactors _ q).app (K n.as))

end SerrePositivity.Asymptotic

end FamilyHomologyTruncationPart

section FamilyPostnikovPart

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type u} [CommRing R] [HasDerivedCategory (ModuleCat.{u} R)]
  (Q : ObjectProperty (ModuleSequence R)) [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]
  (P : (ℕ → DerivedCategory (ModuleCat.{u} R)) → Prop)
  (hiso : ∀ {X Y}, P X → (∀ n, X n ≅ Y n) → P Y)
  (hext : ∀ (T : ℕ → Triangle (DerivedCategory (ModuleCat.{u} R))),
    (∀ n, T n ∈ distTriang _) → P (fun n ↦ (T n).obj₁) →
      P (fun n ↦ (T n).obj₃) → P (fun n ↦ (T n).obj₂))
  (hpure : ∀ (M : ModuleSequence R), Q M → ∀ q : ℤ,
    P (fun n ↦ (DerivedCategory.singleFunctor (ModuleCat R) q).obj (M.obj ⟨n⟩)))

include hiso hpure in
omit [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms] in
/-- 単一次数の場合のホモロジーによる帰着。 -/
lemma familyPostnikov_pure (X : ℕ → DerivedCategory (ModuleCat.{u} R)) (q : ℤ)
    (hge : ∀ n, (X n).IsGE q) (hle : ∀ n, (X n).IsLE q)
    (hH : Q (Discrete.functor
      (fun n ↦ (DerivedCategory.homologyFunctor (ModuleCat R) q).obj (X n)))) : P X :=
  hiso (hpure _ hH q) (fun n ↦ (derivedPureHomologyIso (X n) q).symm)

include hiso hext hpure in
/-- 共通の有限次数幅に関する Postnikov 帰納法。 -/
lemma familyPostnikov_finiteAmplitude (w : ℕ)
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ)
    (hge : ∀ n, (K n).IsStrictlyGE a) (hle : ∀ n, (K n).IsStrictlyLE (a + w))
    (hH : ∀ q, Q (familyHomology K q)) : P (fun n ↦ DerivedCategory.Q.obj (K n)) := by
  induction w generalizing K a with
  | zero =>
    have hle' (n : ℕ) : (K n).IsStrictlyLE a := by simpa using hle n
    exact familyPostnikov_pure Q P hiso hpure _ a (fun n ↦ inferInstance) (fun n ↦ inferInstance)
      (Q.prop_of_iso (familyDerivedHomologyIso K a).symm (hH a))
  | succ w ih =>
    let b : ℤ := a + w
    have hle' (n : ℕ) : (K n).IsStrictlyLE (b + 1) := by
      convert hle n using 1
      dsimp [b]
      omega
    have h₁ : P (fun n ↦ DerivedCategory.Q.obj ((K n).truncLE b)) :=
      ih (fun n ↦ (K n).truncLE b) a (fun n ↦ inferInstance) (fun n ↦ inferInstance)
        (familyHomology_truncLE_prop K Q hH b)
    have h₃ : P (fun n ↦ DerivedCategory.Q.obj ((K n).truncGE (b + 1))) :=
      familyPostnikov_pure Q P hiso hpure _ (b + 1) (fun n ↦ inferInstance) (fun n ↦ inferInstance)
        (Q.prop_of_iso
          (familyDerivedHomologyIso (fun n ↦ (K n).truncGE (b + 1)) (b + 1)).symm
          (familyHomology_truncGE_prop K Q hH (b + 1) (b + 1)))
    exact hext (fun n ↦ DerivedCategory.triangleOfSES ((K n).shortComplexTruncLE_shortExact b))
      (fun n ↦ DerivedCategory.triangleOfSES_distinguished _) h₁
      (hiso h₃ (fun n ↦
        (asIso (DerivedCategory.Q.map ((K n).shortComplexTruncLEX₃ToTruncGE b (b + 1) rfl))).symm))

include hiso hext hpure in
/-- 共通有界な導来対象の族への Postnikov 帰納法。 -/
theorem familyPostnikov_uniform (X : ℕ → DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    (hge : ∀ n, (X n).IsGE a) (hle : ∀ n, (X n).IsLE b)
    (hH : ∀ q, Q (Discrete.functor
      (fun n ↦ (DerivedCategory.homologyFunctor (ModuleCat R) q).obj (X n)))) : P X := by
  choose K hKa hKb he using
    (fun n ↦ DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE (X n) a b)
  have hKb' (n : ℕ) : (K n).IsStrictlyLE (a + (b - a).toNat) :=
    (K n).isStrictlyLE_of_le b _ (by omega)
  have hKH (q : ℤ) : Q (familyHomology K q) := Q.prop_of_iso
    (Discrete.natIso (fun n ↦ (DerivedCategory.homologyFunctor _ q).mapIso (he n.as).some) ≪≫
      familyDerivedHomologyIso K q) (hH q)
  exact hiso (familyPostnikov_finiteAmplitude Q P hiso hext hpure
    (b - a).toNat K a hKa hKb' hKH) (fun n ↦ (he n).some.symm)

end SerrePositivity.Asymptotic

end FamilyPostnikovPart
