module

public import SerrePositivity.AlgebraicGeometry.ReesProjectiveCoefficientComparison
public import SerrePositivity.AlgebraicGeometry.ProjectivePolynomialCoefficientMapNaturality
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChartDirectSumInclusion

/-!
概要：整数次数へ延ばしてから係数制限した Rees の Čech 比較。
方針：所属の命題で直和の次数を比較し、整数次数の自然性を直接使う。
規約：図式全体を次数の関数等式で移送しない。
使われ方：原典 Stacks 30.20.1 の Hⁱ の直和に対応する Čech 版の自然な Rees 比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
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

local instance reesIntegerCechPieceAddGroup (n : ℕ) : AddCommGroup
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).addCommGroup
local instance reesIntegerCechPieceSMul (n : ℕ) : SMul R
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).module.toSMul
local instance reesIntegerCechPieceModule (n : ℕ) : Module R
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).module
local instance reesIntegerCechPiecePolynomialModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
local instance reesIntegerCechPieceTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance reesIntegerCechTotalSMul : SMul R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesAdicTotalBaseModule (ι := ι) (M := M) I).toSMul
local instance reesIntegerCechTotalModule : Module R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule (ι := ι) (M := M) I
local instance reesIntegerCechPolynomialTower : IsScalarTower R (MvPolynomial ι R)
    (ReesAdicTotalModule (ι := ι) (M := M) I) := IsScalarTower.of_compHom _ _ _
local instance reesIntegerCechTotalReesSMul : SMul (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesExtendedModule (S := MvPolynomial ι R) (M := M) I).toSMul
local instance reesIntegerCechTotalReesModule : Module (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesExtendedModule (S := MvPolynomial ι R) (M := M) I
local instance reesIntegerCechTotalReesTower : IsScalarTower R (reesAlgebra I)
    (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule_scalarTower (ι := ι) (M := M) I

local instance reesIntegerCechPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I)) :=
  reesPolynomialCoefficientAlgebra (ι := ι) I
local instance reesIntegerCechRingTower :
    IsScalarTower R (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I)) :=
  reesPolynomialCoefficientAlgebra_scalarTower (ι := ι) I
local instance reesIntegerCechModule :
    Module (MvPolynomial ι (reesAlgebra I)) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  Module.compHom _ (reesPolynomialBaseChange (ι := ι) I)
local instance reesIntegerCechSourceTower :
    IsScalarTower (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_source_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesIntegerCechBaseTower :
    IsScalarTower R (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_base_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesIntegerCechReesTower :
    IsScalarTower (reesAlgebra I) (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_module_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesIntegerCechBaseGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (fun n ↦ (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G n).restrictScalars R) :=
  reesAdicProjectiveBaseGradedSMul (R := R) (M := M) (ι := ι) I G
local instance reesIntegerCechReesGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι (reesAlgebra I))
      (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G) :=
  reesProjectivePolynomialGradedSMul (R := R) (M := M) (ι := ι) I G

/-- B 上で整数次数へ延ばしてから R に係数制限した、Rees の Proj 次数。 -/
abbrev reesAdicProjectiveIntegerBaseGrade (d : ℤ) :
    Submodule R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (projectiveNatGradingInt
    (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G) d).restrictScalars R

local instance reesIntegerCechPieceNatGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectivePiece (ι := ι) I G n) :=
  reesAdicProjectivePieceGradedSMul (ι := ι) I G n
local instance reesIntegerCechPieceIntGraded (n : ℕ) :
    SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt (reesAdicProjectivePiece (ι := ι) I G n)) :=
  projectiveNatGradingIntSMul (ι := ι) (reesAdicProjectivePiece (ι := ι) I G n)
local instance reesIntegerCechIntReesGraded :
    SetLike.GradedSMul
      (AddMonoidAlgebra.gradeBy (reesAlgebra I) (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt
        (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G)) :=
  projectiveNatGradingIntSMul (R := reesAlgebra I) (ι := ι)
    (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G)
local instance reesIntegerCechIntBaseGraded :
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

/-- 整数次数の対応は、図式の移送ではなく所属の命題として示す。 -/
theorem reesAdicProjectiveIntegerBaseGrade_mem_iff (d : ℤ)
    (x : ⨁ n, reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :
    reesAdicDirectSumPolynomialLinearEquiv (ι := ι) (M := M) I x ∈
        reesAdicProjectiveIntegerBaseGrade (R := R) (M := M) (ι := ι) I G d ↔
      x ∈ projectiveDirectSumSubmodule
        (fun n ↦ projectiveNatGradingInt (reesAdicProjectivePiece (ι := ι) I G n) d) := by
  change _ ∈ (projectiveNatGradingInt
    (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G) d).restrictScalars R ↔ _
  rw [projectiveNatGradingInt_restrictScalars]
  exact projectiveNatGradingInt_directSum_mem_iff
    (R := R) (ι := ι) (κ := ℕ)
    (F := fun n ↦ reesAdicProjectiveSubmodule (ι := ι) (M := M) I n)
    (N := ReesAdicTotalModule (ι := ι) (M := M) I)
    (fun n ↦ reesAdicProjectivePiece (ι := ι) I G n)
    (fun n ↦ (reesProjectiveGrade (R := R) (M := M)
      (S := MvPolynomial ι R) I G n).restrictScalars R)
    (reesAdicDirectSumPolynomialLinearEquiv (ι := ι) (M := M) I)
    (reesAdicDirectSumPolynomialLinearEquiv_projective_mem (R := R) (M := M) (ι := ι) I G)
    d x

/-- 整数次数の R 上の Rees 標準開図式と、各 IⁿM の図式の直和との比較。 -/
def reesAdicProjectiveIntegerBaseChartDirectSumIso (d : ℤ) :=
  projectiveGradedModuleChartDirectSumIso
    (R := R) (ι := ι) (κ := ℕ)
    (F := fun n ↦ reesAdicProjectiveSubmodule (ι := ι) (M := M) I n)
    (N := ReesAdicTotalModule (ι := ι) (M := M) I)
    (fun n ↦ projectiveNatGradingInt (reesAdicProjectivePiece (ι := ι) I G n))
    (reesAdicProjectiveIntegerBaseGrade (R := R) (M := M) (ι := ι) I G)
    (reesAdicDirectSumPolynomialLinearEquiv (ι := ι) (M := M) I)
    (reesAdicProjectiveIntegerBaseGrade_mem_iff (R := R) (M := M) (ι := ι) I G) d

/-- 整数次数の R 上の Rees Čech コホモロジーと、各 IⁿM の直和との比較。
原典 Stacks 30.20.1 の Hⁱ に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesAdicProjectiveIntegerBaseCechHomologyDirectSumIso (d : ℤ) (q : ℕ) :=
  projectiveGradedModuleChartDirectSumCechHomologyIso
    (R := R) (ι := ι) (κ := ℕ)
    (F := fun n ↦ reesAdicProjectiveSubmodule (ι := ι) (M := M) I n)
    (N := ReesAdicTotalModule (ι := ι) (M := M) I)
    (fun n ↦ projectiveNatGradingInt (reesAdicProjectivePiece (ι := ι) I G n))
    (reesAdicProjectiveIntegerBaseGrade (R := R) (M := M) (ι := ι) I G)
    (reesAdicDirectSumPolynomialLinearEquiv (ι := ι) (M := M) I)
    (reesAdicProjectiveIntegerBaseGrade_mem_iff (R := R) (M := M) (ι := ι) I G) d q

/-- 同じ B 上の Čech コホモロジーを R へ制限し、各 IⁿM の直和へ比較する。
原典 Stacks 30.20.1 の Hⁱ に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesAdicProjectiveIntegerCechHomologyDirectSumIso (d : ℤ) (q : ℕ) :=
  (projectiveGradedPolynomialCoefficientChangeCechHomologyIso
    (R := R) (B := reesAlgebra I) (ι := ι)
    (N := ReesAdicTotalModule (ι := ι) (M := M) I)
    (projectiveNatGradingInt
      (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G)) d q).symm ≪≫
    reesAdicProjectiveIntegerBaseCechHomologyDirectSumIso
      (R := R) (M := M) (ι := ι) I G d q

end SerrePositivity.AlgebraicGeometry
