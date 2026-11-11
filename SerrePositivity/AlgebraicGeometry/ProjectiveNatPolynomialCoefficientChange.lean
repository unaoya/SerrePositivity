module

public import SerrePositivity.AlgebraicGeometry.ProjectivePolynomialCoefficientChange
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGrading

/-!
概要：自然数次数の多項式加群の Čech 比較に、係数環の変更を接続する。
方針：負の次数への零延長と係数制限の交換を示し、整数次数の比較へ渡す。
規約：基底環 R と係数環 B の作用を区別する。
使われ方：原典 Stacks 30.20.1 の Hⁱ に対応する Čech 版の Rees 比較の特殊化。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u

section Grading
variable {R B N : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]

/-- 自然数次数を負の次数で零に延ばす操作は、係数制限と交換する。 -/
theorem projectiveNatGradingInt_restrictScalars (H : ℕ → Submodule B N) (d : ℤ) :
    (projectiveNatGradingInt H d).restrictScalars R =
      projectiveNatGradingInt (fun n ↦ (H n).restrictScalars R) d := by
  by_cases h : 0 ≤ d <;> simp [projectiveNatGradingInt, h]

end Grading

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {ι : Type} [DecidableEq ι] [Fintype ι]

local instance projectiveNatCoefficientPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι B) :=
  (MvPolynomial.map (algebraMap R B)).toAlgebra

local instance projectiveNatCoefficientPolynomialTower :
    IsScalarTower R (MvPolynomial ι R) (MvPolynomial ι B) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change MvPolynomial.C (algebraMap R B r) =
    MvPolynomial.map (algebraMap R B) (MvPolynomial.C r)
  rw [MvPolynomial.map_C]

variable {N : Type u} [AddCommGroup N] [Module R N] [Module B N]
variable [Module (MvPolynomial ι R) N] [Module (MvPolynomial ι B) N]
variable [IsScalarTower R B N] [IsScalarTower R (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι B) N] [IsScalarTower B (MvPolynomial ι B) N]
variable [IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B) N]
variable (H : ℕ → Submodule B N)
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B) H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
  (fun n ↦ (H n).restrictScalars R)]

/-- 自然数次数の標準開図式の係数環変更と係数制限の比較。 -/
def projectiveNatPolynomialCoefficientChangeChartIso (d : ℤ) :
    projectiveNatGradedModuleChartDiagram (ι := ι) (fun n ↦ (H n).restrictScalars R) d ≅
      projectiveNatGradedModuleChartDiagram (R := B) (M := N) (ι := ι) H d ⋙
        ModuleCat.restrictScalars (algebraMap R B) := by
  let hR : (fun n ↦ (projectiveNatGradingInt H n).restrictScalars R) =
      projectiveNatGradingInt (fun n ↦ (H n).restrictScalars R) :=
    funext (projectiveNatGradingInt_restrictScalars (R := R) H)
  letI := projectiveNatGradingIntSMul (R := B) (ι := ι) H
  letI := projectiveNatGradingIntSMul (R := R) (ι := ι) (fun n ↦ (H n).restrictScalars R)
  letI : SetLike.GradedSMul
      (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (fun n ↦ (projectiveNatGradingInt H n).restrictScalars R) := by
    rw [hR]
    exact projectiveNatGradingIntSMul (R := R) (ι := ι) (fun n ↦ (H n).restrictScalars R)
  change projectiveGradedModuleChartDiagram (ι := ι)
      (projectiveNatGradingInt (fun n ↦ (H n).restrictScalars R)) d ≅
    projectiveGradedModuleChartDiagram (R := B) (M := N) (ι := ι)
      (projectiveNatGradingInt H) d ⋙ ModuleCat.restrictScalars (algebraMap R B)
  simpa only [hR] using projectiveGradedPolynomialCoefficientChangeChartIso
    (R := R) (B := B) (ι := ι) (N := N) (projectiveNatGradingInt H) d

/-- 自然数次数の Čech コホモロジーについて、係数環変更と係数制限を比較する。
原典 Stacks 30.20.1 の Hⁱ の直和に対応する Čech 版の Rees 比較に使う。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveNatPolynomialCoefficientChangeCechHomologyIso (d : ℤ) (q : ℕ) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).mapIso
    ((fullCechComplexFunctor (R := R) (ι := ι)).mapIso
      (projectiveNatPolynomialCoefficientChangeChartIso
        (R := R) (B := B) (ι := ι) (N := N) H d)) ≪≫
    projectiveCechRestrictScalarsHomologyIso (algebraMap R B)
      (projectiveNatGradedModuleChartDiagram (R := B) (M := N) (ι := ι) H d) q

end SerrePositivity.AlgebraicGeometry
