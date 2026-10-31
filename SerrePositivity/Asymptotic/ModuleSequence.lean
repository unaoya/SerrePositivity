module

public import SerrePositivity.LengthAlgebra.Core
public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Category
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# 共通の冪で消える加群列

加群列を離散圏からの関手として扱い、段ごとの全線形写像を射にする。
共通のイデアルの冪で消える条件は部分対象・商・拡大で閉じる。
拡大では両端の指数の和が中央を消すため、一様性が失われない。
-/

@[expose] public section

universe u

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
