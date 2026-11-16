module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFormsComplete
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineRealization
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Reconstruction
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.Pi
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.AffineCochainModel
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.AffineTotalModel

/-!
# 元の affine line の二つの複体の基底上の完備性

## 概要
元の直和模型と指定された全複体を元の基底環上へ制限すると、p・d 導来完備である。

## 方針
元の各項の完備性と、零延長・直和の指定同型を使う。

## 規約
元の複体の K-flat 性を仮定しない。完備性は元の derived Q の像の条件である。

## 使われ方
Construction 6.1 の半自由模型上の反映へ、元の射の source・target の前提を渡す。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R]

private theorem complete_zero_module (a : R) (M : ModuleCat.{u} R) (hM : IsZero M) :
    IsModuleComplete R a M := by
  haveI := ModuleCat.subsingleton_of_isZero hM
  exact isModuleComplete_of_pow_smul_zero R a M 0 (fun _ => Subsingleton.elim _ _)

private theorem complete_biprod_module (a : R) (M N : ModuleCat.{u} R)
    (hM : IsModuleComplete R a M) (hN : IsModuleComplete R a N) : IsModuleComplete R a (M ⊞ N) := by
  let F : Fin 2 → ModuleCat.{u} R := Fin.cases M (fun _ => N)
  have hF (j : Fin 2) : IsModuleComplete R a (F j) := by
    fin_cases j
    · exact hM
    · exact hN
  let e : (∀ j, F j) ≃ₗ[R] M × N := LinearEquiv.piFinTwo R (fun j => F j)
  exact isModuleComplete_of_linearEquiv R a _ _
    (e.trans (ModuleCat.biprodIsoProd M N).symm.toLinearEquiv) (isModuleComplete_pi R a F hF)

private theorem complete_single_term (a : R) (M : ModuleCat.{u} R) (hM : IsModuleComplete R a M)
    (i j : ℤ) :
    IsModuleComplete R a (((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) i).obj M).X j) := by
  by_cases h : j = i
  · exact isModuleComplete_of_linearEquiv R a _ _
      (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) i M j h).symm.toLinearEquiv hM
  · exact complete_zero_module a _ (HomologicalComplex.isZero_single_obj_X (.up ℤ) i M j h)

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A)

private theorem affineLineFormal_terms_complete (j : ℤ) :
    IsModuleComplete (affineAlgebra P 1) (p : affineAlgebra P 1) ((affineLineFormalModel P).X j) := by
  let R := affineAlgebra P 1
  let M₀ := ModuleCat.of R (affineForms P 1 0)
  let M₁ := ModuleCat.of R (affineForms P 1 1)
  let K := (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj M₀
  let L := (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 1).obj M₁
  have hK := complete_single_term (p : R) M₀ (affineForms_p_complete P 1 0) 0 j
  have hL := complete_single_term (p : R) M₁ (affineForms_p_complete P 1 1) 1 j
  exact isModuleComplete_of_linearEquiv R (p : R) _ _
    (HomologicalComplex.biprodXIso K L j).symm.toLinearEquiv
    (complete_biprod_module (p : R) (K.X j) (L.X j) hK hL)

private theorem affineExtended_terms_complete (hP : IsBoundedPrism P) (r : ℕ) (j : ℤ) :
    IsModuleComplete (affineAlgebra P r) (p : affineAlgebra P r) ((affineHTExtendedComplex P hP r).X j) := by
  by_cases h : 0 ≤ j
  · lift j to ℕ using h
    let e : (affineHTExtendedComplex P hP r).X (j : ℤ) ≅ (affineHTComplex P hP r).X j :=
      (affineHTComplex P hP r).extendXIso ComplexShape.embeddingUpNat rfl
    exact isModuleComplete_of_linearEquiv (affineAlgebra P r) (p : affineAlgebra P r) _ _
      e.symm.toLinearEquiv (affineHTModules_isModuleComplete P hP r ⦋j⦌)
  · exact complete_zero_module (p : affineAlgebra P r) _
      ((affineHTComplex P hP r).isZero_extend_X ComplexShape.embeddingUpNat j (fun n hn => by
        change (n : ℤ) = j at hn
        omega))

private theorem affineTotal_terms_complete (hP : IsBoundedPrism P) (r : ℕ) (j : ℤ) :
    IsModuleComplete (affineAlgebra P r) (p : affineAlgebra P r) ((affineHTTotalComplex P hP r).X j) := by
  let e := (HomologicalComplex.eval (ModuleCat.{u} (affineAlgebra P r)) (.up ℤ) j).mapIso
    (affineHTTotalIso P hP r)
  exact isModuleComplete_of_linearEquiv (affineAlgebra P r) (p : affineAlgebra P r) _ _
    e.symm.toLinearEquiv (affineExtended_terms_complete P hP r j)

/-- 同じ元の affine 係数複体を、元の基底作用へ制限して読む。 -/
abbrev affineComplexOnBase (r : ℕ) (K : CochainComplex (ModuleCat.{u} (affineAlgebra P r)) ℤ) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  ((ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)).mapHomologicalComplex (.up ℤ)).obj K

private theorem affineComplexOnBase_complete_p (r : ℕ)
    (K : CochainComplex (ModuleCat.{u} (affineAlgebra P r)) ℤ)
    (hK : ∀ j, IsModuleComplete (affineAlgebra P r) (p : affineAlgebra P r) (K.X j)) :
    IsComplete A (p : A) (DerivedCategory.Q.obj (affineComplexOnBase P r K)) :=
  isComplete_Q_of_terms A (p : A) _ (fun j => affineRestrictedModule_p_complete P r (K.X j) (hK j))

/-- 元の基底作用へ制限した任意の affine 複体は、元の生成元について導来完備。 -/
theorem affineComplexOnBase_complete_generator (r : ℕ)
    (K : CochainComplex (ModuleCat.{u} (affineAlgebra P r)) ℤ) :
    IsComplete A P.generator (DerivedCategory.Q.obj (affineComplexOnBase P r K)) :=
  isComplete_Q_of_terms A P.generator _ (fun j => affineRestrictedModule_generator_complete P r (K.X j))

/-- 元の affine line の直和模型は、元の基底環上で p 導来完備。 -/
theorem affineLineFormal_complete_p :
    IsComplete A (p : A) (DerivedCategory.Q.obj (affineComplexOnBase P 1 (affineLineFormalModel P))) :=
  affineComplexOnBase_complete_p P 1 _ (affineLineFormal_terms_complete P)

/-- 元の指定全複体は、元の基底環上で p 導来完備。 -/
theorem affineHTTotal_complete_p (hP : IsBoundedPrism P) (r : ℕ) :
    IsComplete A (p : A) (DerivedCategory.Q.obj (affineComplexOnBase P r (affineHTTotalComplex P hP r))) :=
  affineComplexOnBase_complete_p P r _ (affineTotal_terms_complete P hP r)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
