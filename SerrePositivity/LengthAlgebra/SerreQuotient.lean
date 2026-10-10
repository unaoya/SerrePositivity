module

public import SerrePositivity.CommutativeAlgebra.PowTorsionCategory
public import SerrePositivity.PerfectComplex.NormalizedLength
public import SerrePositivity.CategoryTheory.AdditiveLength

/-! # 単一の長さ付き代数の評価先

有限な冪ねじれ加群を零長さの加群で割り、忠実な実数値の長さを得る。
有限性は有限生成性ではなく、与えた長さの有限性である。
また、全ての冪ねじれ加群の商には拡大実数値の長さを降下させる。
-/

@[expose] public section

universe u

namespace SerrePositivity.LengthAlgebra

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject ENNReal

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 冪ねじれ加群の短完全列における長さの加法性。 -/
lemma module_length_add {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) (h₂ : IsPowTorsion J S.X₂) :
    lam.len S.X₂ = lam.len S.X₁ + lam.len S.X₃ :=
  lam.len_add_of_exact _ _ _ S.f.hom S.g.hom hS.moduleCat_injective_f
    hS.moduleCat_surjective_g
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact) h₂

/-- 有限の長さをもつ冪ねじれ加群。 -/
def finiteLengthTorsion : ObjectProperty (ModuleCat.{u} R) :=
  fun M ↦ IsPowTorsion J M ∧ lam.len M ≠ ⊤

instance : (finiteLengthTorsion lam).ContainsZero where
  exists_zero := by
    have : Subsingleton (0 : ModuleCat.{u} R) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_zero _)
    refine ⟨0, isZero_zero _, IsPowTorsion.of_subsingleton, ?_⟩
    rw [lam.len_eq_zero_of_subsingleton]
    exact ENNReal.zero_ne_top

instance : (finiteLengthTorsion lam).IsClosedUnderSubobjects where
  prop_of_mono f _ hN :=
    ⟨IsPowTorsion.of_injective f.hom ((ModuleCat.mono_iff_injective _).mp inferInstance) hN.1,
      ne_top_of_le_ne_top hN.2
        (lam.len_le_of_injective f.hom ((ModuleCat.mono_iff_injective _).mp inferInstance) hN.1)⟩

instance : (finiteLengthTorsion lam).IsClosedUnderQuotients where
  prop_of_epi f _ hM :=
    ⟨IsPowTorsion.of_surjective f.hom ((ModuleCat.epi_iff_surjective _).mp inferInstance) hM.1,
      ne_top_of_le_ne_top hM.2
        (lam.len_le_of_surjective f.hom ((ModuleCat.epi_iff_surjective _).mp inferInstance) hM.1)⟩

instance : (finiteLengthTorsion lam).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have ht := (powTorsionModule J).prop_X₂_of_shortExact hS h₁.1 h₃.1
    refine ⟨ht, ?_⟩
    rw [module_length_add lam hS ht]
    exact ENNReal.add_ne_top.mpr ⟨h₁.2, h₃.2⟩

instance : (finiteLengthTorsion lam).IsSerreClass where

/-- 有限な長さの冪ねじれ加群のアーベル圏。 -/
abbrev FiniteLengthTorsion := (finiteLengthTorsion lam).FullSubcategory

/-- 有限性を確認した対象の実数値の長さ。 -/
noncomputable def finiteLength (M : FiniteLengthTorsion lam) : ℝ := (lam.len M.obj).toReal

lemma finiteLength_nonneg (M : FiniteLengthTorsion lam) : 0 ≤ finiteLength lam M :=
  ENNReal.toReal_nonneg

lemma finiteLength_iso {M N : FiniteLengthTorsion lam} (e : M ≅ N) :
    finiteLength lam M = finiteLength lam N := by
  have h : lam.len M.obj = lam.len N.obj :=
    lam.len_congr _ _ (((finiteLengthTorsion lam).ι).mapIso e).toLinearEquiv
  exact congrArg ENNReal.toReal h

lemma finiteLength_of_isZero (M : FiniteLengthTorsion lam) (hM : IsZero M) :
    finiteLength lam M = 0 := by
  have : Subsingleton M.obj := ModuleCat.isZero_iff_subsingleton.mp
    ((finiteLengthTorsion lam).ι.map_isZero hM)
  simp [finiteLength, lam.len_eq_zero_of_subsingleton]

lemma finiteLength_add {S : ShortComplex (FiniteLengthTorsion lam)} (hS : S.ShortExact) :
    finiteLength lam S.X₂ = finiteLength lam S.X₁ + finiteLength lam S.X₃ := by
  have := hS.mono_f
  have := hS.epi_g
  have h := module_length_add lam (hS.map (finiteLengthTorsion lam).ι) S.X₂.property.1
  change lam.len S.X₂.obj = lam.len S.X₁.obj + lam.len S.X₃.obj at h
  dsimp only [finiteLength]
  rw [h, ENNReal.toReal_add S.X₁.property.2 S.X₃.property.2]

instance : (zeroAdditiveLength (finiteLength lam)).IsSerreClass :=
  zeroAdditiveLength_isSerreClass (finiteLength lam) (finiteLength_add lam)
    (finiteLength_nonneg lam) (finiteLength_of_isZero lam _ (isZero_zero _))

/-- 有限な長さの冪ねじれ加群を零長さで割ったアーベル圏。 -/
abbrev FiniteLengthQuotient := (zeroAdditiveLength (finiteLength lam)).isoModSerre.Localization

/-- 有限な長さの商への完全関手。 -/
noncomputable abbrev finiteLengthQuotientFunctor :
    FiniteLengthTorsion lam ⥤ FiniteLengthQuotient lam :=
  (zeroAdditiveLength (finiteLength lam)).isoModSerre.Q

noncomputable instance : PreservesFiniteLimits (finiteLengthQuotientFunctor lam) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteLimits
    (finiteLengthQuotientFunctor lam) (zeroAdditiveLength (finiteLength lam))

noncomputable instance : PreservesFiniteColimits (finiteLengthQuotientFunctor lam) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteColimits
    (finiteLengthQuotientFunctor lam) (zeroAdditiveLength (finiteLength lam))

/-- 有限商の実数値の長さ。 -/
noncomputable def quotientLength : FiniteLengthQuotient lam → ℝ :=
  serreQuotientLength (zeroAdditiveLength (finiteLength lam)) (finiteLength lam)

@[simp] lemma quotientLength_obj (M : FiniteLengthTorsion lam) :
    quotientLength lam ((finiteLengthQuotientFunctor lam).obj M) = (lam.len M.obj).toReal := rfl

lemma quotientLength_nonneg (X : FiniteLengthQuotient lam) : 0 ≤ quotientLength lam X :=
  finiteLength_nonneg lam _

lemma quotientLength_iso {X Y : FiniteLengthQuotient lam} (e : X ≅ Y) :
    quotientLength lam X = quotientLength lam Y :=
  serreQuotientLength_iso (zeroAdditiveLength (finiteLength lam)) (finiteLength lam)
    (finiteLength_iso lam) (finiteLength_add lam) (fun _ h ↦ h) e

lemma quotientLength_add {S : ShortComplex (FiniteLengthQuotient lam)} (hS : S.ShortExact) :
    quotientLength lam S.X₂ = quotientLength lam S.X₁ + quotientLength lam S.X₃ :=
  serreQuotientLength_add (zeroAdditiveLength (finiteLength lam)) (finiteLength lam)
    (finiteLength_iso lam) (finiteLength_add lam) (fun _ h ↦ h) hS

lemma quotientLength_eq_zero_iff (X : FiniteLengthQuotient lam) :
    quotientLength lam X = 0 ↔ IsZero X :=
  serreQuotientLength_eq_zero_iff (zeroAdditiveLength (finiteLength lam)) (finiteLength lam)
    (fun _ ↦ Iff.rfl) X

lemma finiteLengthQuotient_isZero_iff (M : FiniteLengthTorsion lam) :
    IsZero ((finiteLengthQuotientFunctor lam).obj M) ↔ lam.len M.obj = 0 := by
  rw [← quotientLength_eq_zero_iff, quotientLength_obj, ENNReal.toReal_eq_zero_iff]
  simp only [M.property.2, or_false]

/-- 全ての冪ねじれ加群に定義された、無限値を許す長さ。 -/
def torsionLength (M : PowTorsionModule J) : ℝ≥0∞ := lam.len M.obj

lemma torsionLength_iso {M N : PowTorsionModule J} (e : M ≅ N) :
    torsionLength lam M = torsionLength lam N :=
  lam.len_congr _ _ ((powTorsionModule J).ι.mapIso e).toLinearEquiv

lemma torsionLength_of_isZero (M : PowTorsionModule J) (hM : IsZero M) :
    torsionLength lam M = 0 := by
  have : Subsingleton M.obj := ModuleCat.isZero_iff_subsingleton.mp
    ((powTorsionModule J).ι.map_isZero hM)
  exact lam.len_eq_zero_of_subsingleton _

lemma torsionLength_add {S : ShortComplex (PowTorsionModule J)} (hS : S.ShortExact) :
    torsionLength lam S.X₂ = torsionLength lam S.X₁ + torsionLength lam S.X₃ := by
  have := hS.mono_f
  have := hS.epi_g
  exact module_length_add lam (hS.map (powTorsionModule J).ι) S.X₂.property

instance : (zeroAdditiveLength (torsionLength lam)).IsSerreClass :=
  zeroAdditiveLength_isSerreClass (torsionLength lam) (torsionLength_add lam)
    (fun _ ↦ bot_le) (torsionLength_of_isZero lam _ (isZero_zero _))

/-- 無限長も含む冪ねじれ加群を、零長さで割った商。 -/
abbrev LengthQuotient := (zeroAdditiveLength (torsionLength lam)).isoModSerre.Localization

noncomputable abbrev lengthQuotientFunctor : PowTorsionModule J ⥤ LengthQuotient lam :=
  (zeroAdditiveLength (torsionLength lam)).isoModSerre.Q

noncomputable instance : PreservesFiniteLimits (lengthQuotientFunctor lam) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteLimits
    (lengthQuotientFunctor lam) (zeroAdditiveLength (torsionLength lam))

noncomputable instance : PreservesFiniteColimits (lengthQuotientFunctor lam) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteColimits
    (lengthQuotientFunctor lam) (zeroAdditiveLength (torsionLength lam))

/-- 大きな商に降下した非負拡大実数値の長さ。 -/
noncomputable def extendedQuotientLength : LengthQuotient lam → ℝ≥0∞ :=
  serreQuotientLength (zeroAdditiveLength (torsionLength lam)) (torsionLength lam)

@[simp] lemma extendedQuotientLength_obj (M : PowTorsionModule J) :
    extendedQuotientLength lam ((lengthQuotientFunctor lam).obj M) = lam.len M.obj := rfl

lemma extendedQuotientLength_iso {X Y : LengthQuotient lam} (e : X ≅ Y) :
    extendedQuotientLength lam X = extendedQuotientLength lam Y :=
  serreQuotientLength_iso (zeroAdditiveLength (torsionLength lam)) (torsionLength lam)
    (torsionLength_iso lam) (torsionLength_add lam) (fun _ h ↦ h) e

lemma extendedQuotientLength_add {S : ShortComplex (LengthQuotient lam)} (hS : S.ShortExact) :
    extendedQuotientLength lam S.X₂ =
      extendedQuotientLength lam S.X₁ + extendedQuotientLength lam S.X₃ :=
  serreQuotientLength_add (zeroAdditiveLength (torsionLength lam)) (torsionLength lam)
    (torsionLength_iso lam) (torsionLength_add lam) (fun _ h ↦ h) hS

lemma extendedQuotientLength_eq_zero_iff (X : LengthQuotient lam) :
    extendedQuotientLength lam X = 0 ↔ IsZero X :=
  serreQuotientLength_eq_zero_iff (zeroAdditiveLength (torsionLength lam)) (torsionLength lam)
    (fun _ ↦ Iff.rfl) X

end SerrePositivity.LengthAlgebra
