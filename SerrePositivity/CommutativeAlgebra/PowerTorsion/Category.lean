module

public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Basic
public import SerrePositivity.CategoryTheory.Abelian.SerreLength
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # 一つのイデアルの冪で消える加群のアーベル圏

## 概要

イデアル J のある冪で消える加群のなす充満部分圏 `PowTorsionModule` が Serre 部分圏であること（完全列の両端が J^a・J^b で消えれば中央は J^(a+b) で消える）を示し、アーベル圏として扱えるようにする。

## 方針

完全列での零化イデアルの冪の加法性 `annihilator_pow_add_of_exact` から閉性を示し、CategoryTheory の Serre 部分圏と長さの枠組みに載せる。

## 規約

CategoryTheory/Abelian/SerreLength に依存するので `PowerTorsion/Basic` と分ける。

## 使われ方

LengthAlgebra の Serre 商と長さ、Asymptotic の加群の列、Almost のねじれの圏。
-/

@[expose] public noncomputable section

universe u

section PowTorsionCategoryPart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

variable {R : Type u} [CommRing R]

/-- 完全列の両端を消すイデアル冪の積は中央を消す。 -/
lemma annihilator_pow_add_of_exact (J : Ideal R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.Exact) (a b : ℕ) (ha : J ^ a ≤ Module.annihilator R S.X₁)
    (hb : J ^ b ≤ Module.annihilator R S.X₃) :
    J ^ (a + b) ≤ Module.annihilator R S.X₂ := by
  rw [pow_add, Ideal.mul_le]
  intro x hx y hy
  rw [Module.mem_annihilator]
  intro m
  have hm : S.g (y • m) = 0 := by
    rw [map_smul]
    exact Module.mem_annihilator.mp (hb hy) (S.g m)
  obtain ⟨m', hm'⟩ := (S.moduleCat_exact_iff.1 hS) (y • m) hm
  rw [mul_smul, ← hm', ← map_smul]
  rw [Module.mem_annihilator.mp (ha hx) m', map_zero]

/-- 加群全体がある一つのイデアル冪で消える条件。 -/
def powTorsionModule (J : Ideal R) : ObjectProperty (ModuleCat.{u} R) :=
  fun M ↦ IsPowTorsion J M

variable (J : Ideal R)

instance : (powTorsionModule J).ContainsZero where
  exists_zero := by
    have : Subsingleton (0 : ModuleCat.{u} R) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_zero _)
    exact ⟨0, isZero_zero _, IsPowTorsion.of_subsingleton⟩

instance : (powTorsionModule J).IsClosedUnderSubobjects where
  prop_of_mono f _ hN := IsPowTorsion.of_injective f.hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance) hN

instance : (powTorsionModule J).IsClosedUnderQuotients where
  prop_of_epi f _ hM := IsPowTorsion.of_surjective f.hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance) hM

instance : (powTorsionModule J).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    obtain ⟨a, ha⟩ := h₁
    obtain ⟨b, hb⟩ := h₃
    refine ⟨a + b, ?_⟩
    rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe] at ha hb ⊢
    exact annihilator_pow_add_of_exact J S hS.exact a b ha hb

instance : (powTorsionModule J).IsSerreClass where

/-- 冪ねじれ加群のアーベル圏。 -/
abbrev PowTorsionModule := (powTorsionModule J).FullSubcategory

end SerrePositivity

end PowTorsionCategoryPart
