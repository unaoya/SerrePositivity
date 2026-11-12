module

public import SerrePositivity.AlgebraicGeometry.ReesIntegerCechInclusion
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChartAdditive

/-!
概要：Rees の整数次数の係数比較で、実際の Rees 係数の作用を追う。
方針：係数比較の自然性にスカラー写像を入れ、単項式の線形な可換式を標準開へ渡す。
規約：基底環 R 上の係数図式の写像と、Rees 環 B 上のスカラー作用を区別する。
使われ方：Čech コホモロジーの直和で、Rees 単項式が次数を移すことの入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped DirectSum

universe u
variable {R M : Type u} {ι : Type} [CommRing R] [DecidableEq ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance reesIntegerActionCechPieceAddGroup (n : ℕ) : AddCommGroup
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).addCommGroup
local instance reesIntegerActionCechPieceSMul (n : ℕ) : SMul R
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).module.toSMul
local instance reesIntegerActionCechPieceModule (n : ℕ) : Module R
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).module
local instance reesIntegerActionCechPiecePolynomialModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
local instance reesIntegerActionCechPieceTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance reesIntegerActionCechTotalSMul : SMul R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesAdicTotalBaseModule (ι := ι) (M := M) I).toSMul
local instance reesIntegerActionCechTotalModule : Module R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule (ι := ι) (M := M) I
local instance reesIntegerActionCechPolynomialTower : IsScalarTower R (MvPolynomial ι R)
    (ReesAdicTotalModule (ι := ι) (M := M) I) := IsScalarTower.of_compHom _ _ _
local instance reesIntegerActionCechTotalReesSMul : SMul (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesExtendedModule (S := MvPolynomial ι R) (M := M) I).toSMul
local instance reesIntegerActionCechTotalReesModule : Module (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesExtendedModule (S := MvPolynomial ι R) (M := M) I
local instance reesIntegerActionCechTotalReesTower : IsScalarTower R (reesAlgebra I)
    (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule_scalarTower (ι := ι) (M := M) I

local instance reesIntegerActionCechPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I)) :=
  reesPolynomialCoefficientAlgebra (ι := ι) I
local instance reesIntegerActionCechRingTower :
    IsScalarTower R (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I)) :=
  reesPolynomialCoefficientAlgebra_scalarTower (ι := ι) I
local instance reesIntegerActionCechModule :
    Module (MvPolynomial ι (reesAlgebra I)) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  Module.compHom _ (reesPolynomialBaseChange (ι := ι) I)
local instance reesIntegerActionCechSourceTower :
    IsScalarTower (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_source_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesIntegerActionCechBaseTower :
    IsScalarTower R (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_base_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesIntegerActionCechReesTower :
    IsScalarTower (reesAlgebra I) (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_module_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesIntegerActionCechBaseGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (fun n ↦ (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G n).restrictScalars R) :=
  reesAdicProjectiveBaseGradedSMul (R := R) (M := M) (ι := ι) I G
local instance reesIntegerActionCechReesGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι (reesAlgebra I))
      (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G) :=
  reesProjectivePolynomialGradedSMul (R := R) (M := M) (ι := ι) I G

local instance reesIntegerActionCechPieceNatGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectivePiece (ι := ι) I G n) :=
  reesAdicProjectivePieceGradedSMul (ι := ι) I G n
local instance reesIntegerActionCechPieceIntGraded (n : ℕ) :
    SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt (reesAdicProjectivePiece (ι := ι) I G n)) :=
  projectiveNatGradingIntSMul (ι := ι) (reesAdicProjectivePiece (ι := ι) I G n)
local instance reesIntegerActionCechIntReesGraded :
    SetLike.GradedSMul
      (AddMonoidAlgebra.gradeBy (reesAlgebra I) (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt
        (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G)) :=
  projectiveNatGradingIntSMul (R := reesAlgebra I) (ι := ι)
    (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G)
local instance reesIntegerActionCechIntBaseGraded :
    SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (reesAdicProjectiveIntegerBaseGrade (R := R) (M := M) (ι := ι) I G) := by
  change SetLike.GradedSMul
    (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
    (fun d ↦ (projectiveNatGradingInt
      (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G) d).restrictScalars R)
  rw [funext (projectiveNatGradingInt_restrictScalars (R := R)
    (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G))]
  exact projectiveNatGradingIntSMul (R := R) (ι := ι)
    (fun d ↦ (reesProjectiveGrade (R := R) (M := M)
      (S := MvPolynomial ι R) I G d).restrictScalars R)

/-- 整数の Proj 次数を固定した、R と B 上の標準開の係数比較。 -/
abbrev reesAdicProjectiveIntegerCoefficientChartIso (d : ℤ) :=
  projectiveGradedPolynomialCoefficientChangeChartIso
    (R := R) (B := reesAlgebra I) (ι := ι)
    (N := ReesAdicTotalModule (ι := ι) (M := M) I)
    (projectiveNatGradingInt
      (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G)) d

/-- Rees 係数 b の作用が誘導する、R 上の標準開図式の自己写像。 -/
def reesAdicProjectiveIntegerBaseScalarChartMap (b : reesAlgebra I) (d : ℤ) :=
  projectiveGradedModuleChartMap (R := R) (ι := ι)
    (reesAdicProjectiveIntegerBaseGrade (R := R) (M := M) (ι := ι) I G)
    (reesAdicProjectiveIntegerBaseGrade (R := R) (M := M) (ι := ι) I G) d
    ((projectiveBaseScalarLinearMap
      (R := reesAlgebra I) (S := MvPolynomial ι (reesAlgebra I))
      (M := ReesAdicTotalModule (ι := ι) (M := M) I) b).restrictScalars (MvPolynomial ι R))
    (fun n m hm ↦ (projectiveNatGradingInt
      (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G) n).smul_mem b hm)

/-- 整数次数の標準開係数比較は、実際の Rees 係数の作用と可換。 -/
theorem reesAdicProjectiveIntegerCoefficientChartIso_scalar (b : reesAlgebra I) (d : ℤ) :
    reesAdicProjectiveIntegerBaseScalarChartMap (R := R) (M := M) (ι := ι) I G b d ≫
      (reesAdicProjectiveIntegerCoefficientChartIso (R := R) (M := M) (ι := ι) I G d).hom =
    (reesAdicProjectiveIntegerCoefficientChartIso (R := R) (M := M) (ι := ι) I G d).hom ≫
      Functor.whiskerRight
        (b • 𝟙 (projectiveGradedModuleChartDiagram
          (R := reesAlgebra I) (ι := ι)
          (projectiveNatGradingInt
            (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G)) d))
        (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))) := by
  simpa only [projectiveGradedModuleChartMap_baseScalar,
    reesAdicProjectiveIntegerBaseScalarChartMap, reesAdicProjectiveIntegerCoefficientChartIso,
    reesAdicProjectiveIntegerBaseGrade] using
    projectiveGradedPolynomialCoefficientChangeChartIso_naturality
      (R := R) (B := reesAlgebra I) (ι := ι)
      (M := ReesAdicTotalModule (ι := ι) (M := M) I)
      (N := ReesAdicTotalModule (ι := ι) (M := M) I)
      (projectiveNatGradingInt
        (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G))
      (projectiveNatGradingInt
        (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G))
      (projectiveBaseScalarLinearMap
        (R := reesAlgebra I) (S := MvPolynomial ι (reesAlgebra I))
        (M := ReesAdicTotalModule (ι := ι) (M := M) I) b)
      (fun n m hm ↦ (projectiveNatGradingInt
        (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G) n).smul_mem b hm) d

/-- R と B 上の整数次数の Rees の Čech コホモロジーの比較。
原典 Stacks 30.20.1 の Hⁱ に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
abbrev reesAdicProjectiveIntegerCoefficientCechHomologyIso (d : ℤ) (q : ℕ) :=
  projectiveGradedPolynomialCoefficientChangeCechHomologyIso
    (R := R) (B := reesAlgebra I) (ι := ι)
    (N := ReesAdicTotalModule (ι := ι) (M := M) I)
    (projectiveNatGradingInt
      (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G)) d q

/-- Čech コホモロジーの係数比較も、実際の Rees スカラー作用と可換。
原典 Stacks 30.20.1 の Hⁱ の Rees 作用に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveIntegerCoefficientCechHomologyIso_scalar
    (b : reesAlgebra I) (d : ℤ) (q : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
        (fullCechComplexMap
          (reesAdicProjectiveIntegerBaseScalarChartMap (R := R) (M := M) (ι := ι) I G b d)) ≫
      (reesAdicProjectiveIntegerCoefficientCechHomologyIso
        (R := R) (M := M) (ι := ι) I G d q).hom =
    (reesAdicProjectiveIntegerCoefficientCechHomologyIso
        (R := R) (M := M) (ι := ι) I G d q).hom ≫
      (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).map
        (b • 𝟙 ((fullCechComplex (projectiveGradedModuleChartDiagram
          (R := reesAlgebra I) (ι := ι)
          (projectiveNatGradingInt
            (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G)) d)).homology q)) := by
  have hs :
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} (reesAlgebra I)) (.up ℕ) q).map
        (fullCechComplexMap (projectiveGradedModuleChartMap (R := reesAlgebra I) (ι := ι)
          (projectiveNatGradingInt
            (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G))
          (projectiveNatGradingInt
            (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G)) d
          (projectiveBaseScalarLinearMap
            (R := reesAlgebra I) (S := MvPolynomial ι (reesAlgebra I))
            (M := ReesAdicTotalModule (ι := ι) (M := M) I) b)
          (fun n m hm ↦ (projectiveNatGradingInt
            (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G) n).smul_mem b hm))) =
      b • 𝟙 ((fullCechComplex (projectiveGradedModuleChartDiagram
        (R := reesAlgebra I) (ι := ι) (projectiveNatGradingInt
          (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G)) d)).homology q) :=
    projectiveGradedModuleCechHomologyMap_baseScalar
      (R := reesAlgebra I) (ι := ι)
      (M := ReesAdicTotalModule (ι := ι) (M := M) I)
      (projectiveNatGradingInt
        (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G)) b d q
  have hn := projectiveGradedPolynomialCoefficientChangeCechHomologyIso_naturality
    (R := R) (B := reesAlgebra I) (ι := ι)
    (M := ReesAdicTotalModule (ι := ι) (M := M) I)
    (N := ReesAdicTotalModule (ι := ι) (M := M) I)
    (projectiveNatGradingInt
      (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G))
    (projectiveNatGradingInt
      (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G))
    (projectiveBaseScalarLinearMap
      (R := reesAlgebra I) (S := MvPolynomial ι (reesAlgebra I))
      (M := ReesAdicTotalModule (ι := ι) (M := M) I) b)
    (fun n m hm ↦ (projectiveNatGradingInt
      (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G) n).smul_mem b hm) d q
  rw [hs] at hn
  simpa only [reesAdicProjectiveIntegerBaseScalarChartMap,
    reesAdicProjectiveIntegerCoefficientCechHomologyIso,
    reesAdicProjectiveIntegerBaseGrade] using hn

/-- Rees 単項式と各次数の包含の可換式を、標準開の図式へ渡す。 -/
theorem reesAdicProjectiveIntegerChartInclusion_monomial
    (i j : ℕ) (a : R) (ha : a ∈ I ^ i) (d : ℤ) :
    reesAdicProjectiveIntegerChartInclusion (R := R) (M := M) (ι := ι) I G d j ≫
      reesAdicProjectiveIntegerBaseScalarChartMap (R := R) (M := M) (ι := ι) I G
        (⟨Polynomial.monomial i a, reesAlgebra.monomial_mem.mpr ha⟩ : reesAlgebra I) d =
    reesAdicProjectiveDegreeShiftChartMap (R := R) (M := M) (ι := ι) I G i j a ha d ≫
      reesAdicProjectiveIntegerChartInclusion (R := R) (M := M) (ι := ι) I G d (i + j) := by
  simp only [reesAdicProjectiveIntegerChartInclusion, projectiveGradedModuleChartInclusion,
    reesAdicProjectiveIntegerBaseScalarChartMap, reesAdicProjectiveDegreeShiftChartMap,
    projectiveNatGradedModuleChartMap]
  rw [projectiveGradedModuleChartMap_comp, projectiveGradedModuleChartMap_comp]
  congr 1
  exact reesAdicProjectiveIntegerCoefficientInclusion_monomial
    (R := R) (M := M) (ι := ι) I i j a ha

end SerrePositivity.AlgebraicGeometry
