module

public import SerrePositivity.AlgebraicGeometry.ReesCechImageFiltration
public import SerrePositivity.AlgebraicGeometry.ReesDirectSumLinearMap
public import SerrePositivity.AlgebraicGeometry.ReesIntegerCechGradedAction
public import SerrePositivity.AlgebraicGeometry.ReesFiltrationModule

/-!
概要：Čech コホモロジーの直和から、実際の像の Rees 加群への全射を作る。
方針：各段の像への全射を直和で組み、単項式の作用との可換性を示す。
規約：ここでは Noether 性や有限生成性を仮定しない。
使われ方：像の Rees 加群の有限性を、射影 Čech コホモロジーの有限性から導く。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped DirectSum

universe u
variable {R M : Type u} {ι : Type} [CommRing R] [LinearOrder ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance reesImageAssemblyPolynomialModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
local instance reesImageAssemblyTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance reesImageAssemblyGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectivePiece (ι := ι) I G n) :=
  reesAdicProjectivePieceGradedSMul (ι := ι) I G n
local instance reesImageAssemblyModule (d : ℤ) (q : ℕ) :
    Module (reesAlgebra I) (ReesIntegerCechDirectSum (ι := ι) I G d q) :=
  reesAdicCechIntegerDirectSumTransportedModule (ι := ι) I G d q

/-- 各段の Čech 像への写像を、像の Rees 加群への R 線形写像に組む。 -/
def reesAdicProjectiveCechImageAssembleR (d : ℤ) (q : ℕ) :
    ReesIntegerCechDirectSum (ι := ι) I G d q →ₗ[R]
      (reesAdicProjectiveCechImageFiltration (ι := ι) I G d q).submodule :=
  (reesFiltrationDirectSumLinearEquiv
    (reesAdicProjectiveCechImageFiltration (ι := ι) I G d q)).toLinearMap.comp
      (DirectSum.lmap (fun n ↦ reesAdicProjectiveCechImageStageMap (ι := ι) I G n d q))

/-- 一つの Čech 成分は、その像を係数とする Rees 単項式に写る。 -/
theorem reesAdicProjectiveCechImageAssembleR_lof (n : ℕ) (d : ℤ) (q : ℕ)
    (x : reesAdicProjectiveCechStage (ι := ι) I G n d q) :
    reesAdicProjectiveCechImageAssembleR (ι := ι) I G d q
        (DirectSum.lof R ℕ (fun j ↦ reesAdicProjectiveCechStage (ι := ι) I G j d q) n x) =
      reesFiltrationSingle (reesAdicProjectiveCechImageFiltration (ι := ι) I G d q) n
        (reesAdicProjectiveCechImageStageMap (ι := ι) I G n d q x) := by
  unfold reesAdicProjectiveCechImageAssembleR
  rw [LinearMap.comp_apply, DirectSum.lmap_lof]
  exact reesFiltrationAssemble_of (R := R) (I := I)
    (reesAdicProjectiveCechImageFiltration (ι := ι) I G d q) n _

/-- 各段の像への全射を組んだ R 線形写像は全射。 -/
theorem reesAdicProjectiveCechImageAssembleR_surjective (d : ℤ) (q : ℕ) :
    Function.Surjective (reesAdicProjectiveCechImageAssembleR (ι := ι) I G d q) := by
  apply (reesFiltrationDirectSumLinearEquiv
    (reesAdicProjectiveCechImageFiltration (ι := ι) I G d q)).surjective.comp
  exact (DirectSum.lmap_surjective _).mpr
    (fun n ↦ reesAdicProjectiveCechImageStageMap_surjective (ι := ι) I G n d q)

/-- Čech 像への直和写像は、単項式と各成分で Rees 作用と可換。 -/
theorem reesAdicProjectiveCechImageAssembleR_monomial_lof
    (i j : ℕ) (a : R) (ha : a ∈ I ^ i) (d : ℤ) (q : ℕ)
    (x : reesAdicProjectiveCechStage (ι := ι) I G j d q) :
    reesAdicProjectiveCechImageAssembleR (ι := ι) I G d q
        ((⟨Polynomial.monomial i a, reesAlgebra.monomial_mem.mpr ha⟩ : reesAlgebra I) •
          DirectSum.lof R ℕ
            (fun n ↦ reesAdicProjectiveCechStage (ι := ι) I G n d q) j x) =
      (⟨Polynomial.monomial i a, reesAlgebra.monomial_mem.mpr ha⟩ : reesAlgebra I) •
        reesAdicProjectiveCechImageAssembleR (ι := ι) I G d q
          (DirectSum.lof R ℕ
            (fun n ↦ reesAdicProjectiveCechStage (ι := ι) I G n d q) j x) := by
  rw [reesAdicCechIntegerDirectSum_monomial_smul_lof (ι := ι) I G i j a ha d q x]
  rw [reesAdicProjectiveCechImageAssembleR_lof, reesAdicProjectiveCechImageAssembleR_lof,
    reesFiltration_monomial_smul_single
      (reesAdicProjectiveCechImageFiltration (ι := ι) I G d q) i j a ha]
  congr 1
  apply Subtype.ext
  have hcat := reesAdicProjectiveCechToModule_degreeShift (ι := ι) I G i j a ha d q
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hcat) x

/-- 各段の Čech 像への写像を組んだ Rees 線形写像。 -/
def reesAdicProjectiveCechImageAssemble (d : ℤ) (q : ℕ) :
    ReesIntegerCechDirectSum (ι := ι) I G d q →ₗ[reesAlgebra I]
      (reesAdicProjectiveCechImageFiltration (ι := ι) I G d q).submodule :=
  reesDirectSumLinearMapOfMonomialLof I
    (reesAdicProjectiveCechImageAssembleR (ι := ι) I G d q)
    (fun i j a ha x ↦
      reesAdicProjectiveCechImageAssembleR_monomial_lof (ι := ι) I G i j a ha d q x)

/-- Čech コホモロジーの直和から、像の Rees 加群への Rees 線形写像は全射。 -/
theorem reesAdicProjectiveCechImageAssemble_surjective (d : ℤ) (q : ℕ) :
    Function.Surjective (reesAdicProjectiveCechImageAssemble (ι := ι) I G d q) :=
  reesAdicProjectiveCechImageAssembleR_surjective (ι := ι) I G d q

end SerrePositivity.AlgebraicGeometry
