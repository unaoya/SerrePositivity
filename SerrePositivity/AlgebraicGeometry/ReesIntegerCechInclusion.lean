module

public import SerrePositivity.AlgebraicGeometry.ReesIntegerCechComparison
public import SerrePositivity.AlgebraicGeometry.ReesExtendedMonomialAction
public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveCechDegreeShift
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChartScalarAction

/-!
概要：各 Rees 次数の包含を、整数次数の標準開・Čech 直和比較へ渡す。
方針：直和同値と lof の合成を使い、単項式の既存の作用公式と照合する。
規約：R 側の Rees の Proj 次数は、B 上の整数次数を R に制限したもの。
使われ方：Čech コホモロジーの直和で Rees 単項式の次数移動を証明する入力。
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

local instance reesIntegerInclusionCechPieceAddGroup (n : ℕ) : AddCommGroup
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).addCommGroup
local instance reesIntegerInclusionCechPieceSMul (n : ℕ) : SMul R
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).module.toSMul
local instance reesIntegerInclusionCechPieceModule (n : ℕ) : Module R
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).module
local instance reesIntegerInclusionCechPiecePolynomialModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
local instance reesIntegerInclusionCechPieceTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance reesIntegerInclusionCechTotalSMul : SMul R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesAdicTotalBaseModule (ι := ι) (M := M) I).toSMul
local instance reesIntegerInclusionCechTotalModule : Module R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule (ι := ι) (M := M) I
local instance reesIntegerInclusionCechPolynomialTower : IsScalarTower R (MvPolynomial ι R)
    (ReesAdicTotalModule (ι := ι) (M := M) I) := IsScalarTower.of_compHom _ _ _
local instance reesIntegerInclusionCechTotalReesSMul : SMul (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesExtendedModule (S := MvPolynomial ι R) (M := M) I).toSMul
local instance reesIntegerInclusionCechTotalReesModule : Module (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesExtendedModule (S := MvPolynomial ι R) (M := M) I
local instance reesIntegerInclusionCechTotalReesTower : IsScalarTower R (reesAlgebra I)
    (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule_scalarTower (ι := ι) (M := M) I

local instance reesIntegerInclusionCechPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I)) :=
  reesPolynomialCoefficientAlgebra (ι := ι) I
local instance reesIntegerInclusionCechRingTower :
    IsScalarTower R (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I)) :=
  reesPolynomialCoefficientAlgebra_scalarTower (ι := ι) I
local instance reesIntegerInclusionCechModule :
    Module (MvPolynomial ι (reesAlgebra I)) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  Module.compHom _ (reesPolynomialBaseChange (ι := ι) I)
local instance reesIntegerInclusionCechSourceTower :
    IsScalarTower (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_source_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesIntegerInclusionCechBaseTower :
    IsScalarTower R (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_base_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesIntegerInclusionCechReesTower :
    IsScalarTower (reesAlgebra I) (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_module_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesIntegerInclusionCechBaseGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (fun n ↦ (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G n).restrictScalars R) :=
  reesAdicProjectiveBaseGradedSMul (R := R) (M := M) (ι := ι) I G
local instance reesIntegerInclusionCechReesGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι (reesAlgebra I))
      (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G) :=
  reesProjectivePolynomialGradedSMul (R := R) (M := M) (ι := ι) I G

local instance reesIntegerInclusionCechPieceNatGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectivePiece (ι := ι) I G n) :=
  reesAdicProjectivePieceGradedSMul (ι := ι) I G n
local instance reesIntegerInclusionCechPieceIntGraded (n : ℕ) :
    SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt (reesAdicProjectivePiece (ι := ι) I G n)) :=
  projectiveNatGradingIntSMul (ι := ι) (reesAdicProjectivePiece (ι := ι) I G n)
local instance reesIntegerInclusionCechIntReesGraded :
    SetLike.GradedSMul
      (AddMonoidAlgebra.gradeBy (reesAlgebra I) (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt
        (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G)) :=
  projectiveNatGradingIntSMul (R := reesAlgebra I) (ι := ι)
    (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G)
local instance reesIntegerInclusionCechIntBaseGraded :
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

/-- 各 IⁿM から Rees 加群への、多項式環上線形な包含。 -/
abbrev reesAdicProjectiveIntegerCoefficientInclusion (n : ℕ) :=
  (reesAdicDirectSumPolynomialLinearEquiv (ι := ι) (M := M) I).toLinearMap.comp
    (DirectSum.lof (MvPolynomial ι R) ℕ
      (fun j ↦ reesAdicProjectiveSubmodule (ι := ι) (M := M) I j) n)

/-- 上の包含は、Rees 加群の第 n 単項式を作る。 -/
theorem reesAdicProjectiveIntegerCoefficientInclusion_apply (n : ℕ)
    (m : reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :
    reesAdicProjectiveIntegerCoefficientInclusion (ι := ι) (M := M) I n m =
      reesFiltrationSingle
        ((I.map (algebraMap R (MvPolynomial ι R))).stableFiltration
          (⊤ : Submodule (MvPolynomial ι R) M)) n m :=
  reesFiltrationAssemble_of (R := MvPolynomial ι R) (M := M)
    (I := I.map (algebraMap R (MvPolynomial ι R)))
    ((I.map (algebraMap R (MvPolynomial ι R))).stableFiltration
      (⊤ : Submodule (MvPolynomial ι R) M)) n m

/-- 各 IⁿM の包含が誘導する、整数次数の標準開図式の写像。 -/
def reesAdicProjectiveIntegerChartInclusion (d : ℤ) (n : ℕ) :=
  projectiveGradedModuleChartInclusion
    (R := R) (ι := ι) (κ := ℕ)
    (F := fun j ↦ reesAdicProjectiveSubmodule (ι := ι) (M := M) I j)
    (N := ReesAdicTotalModule (ι := ι) (M := M) I)
    (fun j ↦ projectiveNatGradingInt (reesAdicProjectivePiece (ι := ι) I G j))
    (reesAdicProjectiveIntegerBaseGrade (R := R) (M := M) (ι := ι) I G)
    (reesAdicDirectSumPolynomialLinearEquiv (ι := ι) (M := M) I)
    (reesAdicProjectiveIntegerBaseGrade_mem_iff (R := R) (M := M) (ι := ι) I G) d n

/-- Rees の標準開直和比較は、各次数の包含を係数図式の直和の包含へ送る。 -/
theorem reesAdicProjectiveIntegerBaseChartDirectSumIso_inclusion (d : ℤ) (n : ℕ) :
    reesAdicProjectiveIntegerChartInclusion (R := R) (M := M) (ι := ι) I G d n ≫
      (reesAdicProjectiveIntegerBaseChartDirectSumIso (R := R) (M := M) (ι := ι) I G d).hom =
    projectiveCechDirectSumDiagramInclusion
      (fun j ↦ projectiveNatGradedModuleChartDiagram (ι := ι)
        (reesAdicProjectivePiece (ι := ι) I G j) d) n := by
  exact projectiveGradedModuleChartDirectSumIso_inclusion
    (R := R) (ι := ι) (κ := ℕ)
    (F := fun j ↦ reesAdicProjectiveSubmodule (ι := ι) (M := M) I j)
    (N := ReesAdicTotalModule (ι := ι) (M := M) I)
    (fun j ↦ projectiveNatGradingInt (reesAdicProjectivePiece (ι := ι) I G j))
    (reesAdicProjectiveIntegerBaseGrade (R := R) (M := M) (ι := ι) I G)
    (reesAdicDirectSumPolynomialLinearEquiv (ι := ι) (M := M) I)
    (reesAdicProjectiveIntegerBaseGrade_mem_iff (R := R) (M := M) (ι := ι) I G) d n

/-- Rees の Čech 直和比較は、各次数の包含をコホモロジーの直和の lof に送る。
原典 Stacks 30.20.1 の Hⁱ の直和比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveIntegerBaseCechHomologyDirectSumIso_inclusion
    (d : ℤ) (q : ℕ) (n : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
        (fullCechComplexMap
          (reesAdicProjectiveIntegerChartInclusion (R := R) (M := M) (ι := ι) I G d n)) ≫
      (reesAdicProjectiveIntegerBaseCechHomologyDirectSumIso
        (R := R) (M := M) (ι := ι) I G d q).hom =
    ModuleCat.ofHom (DirectSum.lof R ℕ
      (fun j ↦ (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι)
        (reesAdicProjectivePiece (ι := ι) I G j) d)).homology q) n) := by
  exact projectiveGradedModuleChartDirectSumCechHomologyIso_inclusion
    (R := R) (ι := ι) (κ := ℕ)
    (F := fun j ↦ reesAdicProjectiveSubmodule (ι := ι) (M := M) I j)
    (N := ReesAdicTotalModule (ι := ι) (M := M) I)
    (fun j ↦ projectiveNatGradingInt (reesAdicProjectivePiece (ι := ι) I G j))
    (reesAdicProjectiveIntegerBaseGrade (R := R) (M := M) (ι := ι) I G)
    (reesAdicDirectSumPolynomialLinearEquiv (ι := ι) (M := M) I)
    (reesAdicProjectiveIntegerBaseGrade_mem_iff (R := R) (M := M) (ι := ι) I G) d q n

/-- Rees 単項式の作用と各次数の包含が作る、多項式環上線形な可換式。 -/
theorem reesAdicProjectiveIntegerCoefficientInclusion_monomial
    (i j : ℕ) (a : R) (ha : a ∈ I ^ i) :
    ((projectiveBaseScalarLinearMap
      (R := reesAlgebra I) (S := MvPolynomial ι (reesAlgebra I))
      (M := ReesAdicTotalModule (ι := ι) (M := M) I)
      (⟨Polynomial.monomial i a, reesAlgebra.monomial_mem.mpr ha⟩ : reesAlgebra I)).restrictScalars
        (MvPolynomial ι R)).comp
      (reesAdicProjectiveIntegerCoefficientInclusion (ι := ι) (M := M) I j) =
    (reesAdicProjectiveIntegerCoefficientInclusion (ι := ι) (M := M) I (i + j)).comp
      (reesAdicProjectiveDegreeShift (ι := ι) (M := M) I i j a ha) := by
  apply LinearMap.ext
  intro m
  change (⟨Polynomial.monomial i a, reesAlgebra.monomial_mem.mpr ha⟩ : reesAlgebra I) •
      reesAdicProjectiveIntegerCoefficientInclusion (ι := ι) (M := M) I j m =
    reesAdicProjectiveIntegerCoefficientInclusion (ι := ι) (M := M) I (i + j)
      (reesAdicProjectiveDegreeShift (ι := ι) (M := M) I i j a ha m)
  rw [reesAdicProjectiveIntegerCoefficientInclusion_apply,
    reesAdicProjectiveIntegerCoefficientInclusion_apply]
  rw [reesExtendedModule_monomial_smul_single (S := MvPolynomial ι R) I i j a ha m]
  congr 1
  apply Subtype.ext
  exact algebraMap_smul (MvPolynomial ι R) a m.val

end SerrePositivity.AlgebraicGeometry
