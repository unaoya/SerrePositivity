module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFormsProjective
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBasePolynomialAction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Presentation
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFormsProjective
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBasePolynomialAction

/-!
# 元の affine 形式の完備性と基底係数の制限

## 概要
元の完備形式の p 完備性と、元の基底作用へ制限した際の p・d 完備性を確認する。

## 方針
元の完備化の漸化式と有限表示加群の完備性を使う。d は元の剰余係数射で零となる。

## 規約
基底環への制限は元の affineBaseToPolynomialMap によるもの。

## 使われ方
Construction 6.1 の反映へ渡す元の affine line の複体の完備性。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (r : ℕ)

/-- 元の affine 完備多項式環は、自分自身の p 作用について導来完備。 -/
theorem affineAlgebra_p_complete :
    IsModuleComplete (affineAlgebra P r) (p : affineAlgebra P r)
      (ModuleCat.of (affineAlgebra P r) (affineAlgebra P r)) := by
  let B := MvPolynomial (Fin r) (A ⧸ P.ideal)
  letI : Algebra B (affineAlgebra P r) :=
    (principalCompletionUnitRingHom B (p : B)).toAlgebra
  letI : Module B (affineAlgebra P r) := Algebra.toModule
  letI : IsScalarTower B (affineAlgebra P r) (affineAlgebra P r) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have h := principalCompletion_isModuleComplete_unit (R := B) (p : B)
  simpa only [map_natCast] using
    (isModuleComplete_algebraMap_iff B (affineAlgebra P r) (p : B) (affineAlgebra P r)).mpr h

/-- 元の完備形式も、元の affine 係数作用の p について導来完備。 -/
theorem affineForms_p_complete (i : ℕ) :
    IsModuleComplete (affineAlgebra P r) (p : affineAlgebra P r)
      (ModuleCat.of (affineAlgebra P r) (affineForms P r i)) := by
  haveI := affineForms_finite P r i
  haveI : Module.Projective (affineAlgebra P r) (affineForms P r i) :=
    Module.Projective.of_basis (affineCompletedFormsBasis P r i)
  haveI := Module.finitePresentation_of_projective (affineAlgebra P r) (affineForms P r i)
  exact isModuleComplete_of_finitePresentation (affineAlgebra P r) (p : affineAlgebra P r)
    (affineAlgebra_p_complete P r) (ModuleCat.of (affineAlgebra P r) (affineForms P r i))

/-- 元の基底生成元は、元の affine 剰余係数射で零となる。 -/
theorem affineBaseToPolynomialMap_generator : affineBaseToPolynomialMap P r P.generator = 0 := by
  have h : Ideal.Quotient.mk P.ideal P.generator = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  simp only [affineBaseToPolynomialMap, RingHom.comp_apply, h, map_zero]

/-- 元の基底作用への制限は、同じ p 作用の導来完備性を保つ。 -/
theorem affineRestrictedModule_p_complete (M : ModuleCat.{u} (affineAlgebra P r))
    (h : IsModuleComplete (affineAlgebra P r) (p : affineAlgebra P r) M) :
    IsModuleComplete A (p : A) ((ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).obj M) := by
  letI := Module.compHom M (affineBaseToPolynomialMap P r)
  rw [isModuleComplete_iff_recurrence_bijective] at h ⊢
  change Function.Bijective (adicRecurrenceMap (M := M) (p : A))
  have he : (adicRecurrenceMap (M := M) (p : A) : (ℕ → M) → (ℕ → M)) =
      (adicRecurrenceMap (M := M) (p : affineAlgebra P r) : (ℕ → M) → (ℕ → M)) := by
    funext x n
    change x n - (p : A) • x (n + 1) = x n - (p : affineAlgebra P r) • x (n + 1)
    simp only [Nat.cast_smul_eq_nsmul]
  rw [he]
  exact h

/-- 元の基底作用へ制限した任意の affine 加群は、元の生成元の作用について導来完備。 -/
theorem affineRestrictedModule_generator_complete (M : ModuleCat.{u} (affineAlgebra P r)) :
    IsModuleComplete A P.generator
      ((ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).obj M) := by
  apply isModuleComplete_of_pow_smul_zero A P.generator _ 1
  intro x
  rw [pow_one]
  change affineBaseToPolynomialMap P r P.generator • x = 0
  rw [affineBaseToPolynomialMap_generator, zero_smul]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
