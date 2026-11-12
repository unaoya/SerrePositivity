module

public import SerrePositivity.AlgebraicGeometry.ReesIntegerCechComponentAction
public import SerrePositivity.AlgebraicGeometry.ProjectiveScalarRestrictionTransportComponent

/-!
概要：Čech コホモロジーの直和へ移した Rees 作用の次数付き性と有限性。
方針：成分写像の可換式で単項式の作用を計算し、斉次部分の作用を判定する。
規約：Proj 次数 d と Čech 次数 q を固定し、Rees 次数は外部直和の添字とする。
使われ方：実際の像・核の Rees 加群を有限生成性へ接続する入力。
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

local instance reesIntegerGradedCechPieceAddGroup (n : ℕ) : AddCommGroup
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).addCommGroup
local instance reesIntegerGradedCechPieceSMul (n : ℕ) : SMul R
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).module.toSMul
local instance reesIntegerGradedCechPieceModule (n : ℕ) : Module R
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).module
local instance reesIntegerGradedCechPiecePolynomialModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
local instance reesIntegerGradedCechPieceTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance reesIntegerGradedCechTotalSMul : SMul R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesAdicTotalBaseModule (ι := ι) (M := M) I).toSMul
local instance reesIntegerGradedCechTotalModule : Module R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule (ι := ι) (M := M) I
local instance reesIntegerGradedCechPolynomialTower : IsScalarTower R (MvPolynomial ι R)
    (ReesAdicTotalModule (ι := ι) (M := M) I) := IsScalarTower.of_compHom _ _ _
local instance reesIntegerGradedCechTotalReesSMul : SMul (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesExtendedModule (S := MvPolynomial ι R) (M := M) I).toSMul
local instance reesIntegerGradedCechTotalReesModule : Module (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesExtendedModule (S := MvPolynomial ι R) (M := M) I
local instance reesIntegerGradedCechTotalReesTower : IsScalarTower R (reesAlgebra I)
    (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule_scalarTower (ι := ι) (M := M) I

local instance reesIntegerGradedCechPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I)) :=
  reesPolynomialCoefficientAlgebra (ι := ι) I
local instance reesIntegerGradedCechRingTower :
    IsScalarTower R (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I)) :=
  reesPolynomialCoefficientAlgebra_scalarTower (ι := ι) I
local instance reesIntegerGradedCechModule :
    Module (MvPolynomial ι (reesAlgebra I)) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  Module.compHom _ (reesPolynomialBaseChange (ι := ι) I)
local instance reesIntegerGradedCechSourceTower :
    IsScalarTower (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_source_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesIntegerGradedCechBaseTower :
    IsScalarTower R (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_base_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesIntegerGradedCechReesTower :
    IsScalarTower (reesAlgebra I) (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_module_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesIntegerGradedCechBaseGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (fun n ↦ (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G n).restrictScalars R) :=
  reesAdicProjectiveBaseGradedSMul (R := R) (M := M) (ι := ι) I G
local instance reesIntegerGradedCechReesGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι (reesAlgebra I))
      (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G) :=
  reesProjectivePolynomialGradedSMul (R := R) (M := M) (ι := ι) I G

local instance reesIntegerGradedCechPieceNatGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectivePiece (ι := ι) I G n) :=
  reesAdicProjectivePieceGradedSMul (ι := ι) I G n
local instance reesIntegerGradedCechPieceIntGraded (n : ℕ) :
    SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt (reesAdicProjectivePiece (ι := ι) I G n)) :=
  projectiveNatGradingIntSMul (ι := ι) (reesAdicProjectivePiece (ι := ι) I G n)
local instance reesIntegerGradedCechIntReesGraded :
    SetLike.GradedSMul
      (AddMonoidAlgebra.gradeBy (reesAlgebra I) (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt
        (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G)) :=
  projectiveNatGradingIntSMul (R := reesAlgebra I) (ι := ι)
    (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G)
local instance reesIntegerGradedCechIntBaseGraded :
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

/-- 各 IⁿM の同じ Proj・Čech 次数のコホモロジーの直和。 -/
abbrev ReesIntegerCechDirectSum (d : ℤ) (q : ℕ) :=
  ⨁ n, (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι)
    (reesAdicProjectivePiece (ι := ι) I G n) d)).homology q

/-- 自然な整数次数の比較に沿って、Čech コホモロジーの直和に Rees 作用を移す。 -/
@[instance_reducible]
def reesAdicCechIntegerDirectSumTransportedModule (d : ℤ) (q : ℕ) :
    Module (reesAlgebra I) (ReesIntegerCechDirectSum (R := R) (M := M) (ι := ι) I G d q) :=
  projectiveScalarRestrictionTransportModuleOfIso
    (reesAdicProjectiveIntegerCechObject (R := R) (M := M) (ι := ι) I G d q)
    (reesAdicProjectiveIntegerCechHomologyDirectSumIso (R := R) (M := M) (ι := ι) I G d q)

/-- 移した Rees 作用は、直和の既存の R 作用と両立する。 -/
theorem reesAdicCechIntegerDirectSumTransportedScalarTower (d : ℤ) (q : ℕ) :
    letI := reesAdicCechIntegerDirectSumTransportedModule (R := R) (M := M) (ι := ι) I G d q
    IsScalarTower R (reesAlgebra I)
      (ReesIntegerCechDirectSum (R := R) (M := M) (ι := ι) I G d q) :=
  projectiveScalarRestrictionTransportOfIso_scalarTower
    (reesAdicProjectiveIntegerCechObject (R := R) (M := M) (ι := ι) I G d q)
    (reesAdicProjectiveIntegerCechHomologyDirectSumIso (R := R) (M := M) (ι := ι) I G d q)

/-- 整数次数の比較に沿って移した作用に関する B 線形同値。 -/
def reesAdicCechIntegerDirectSumTransportedLinearEquiv (d : ℤ) (q : ℕ) :=
  projectiveScalarRestrictionTransportLinearEquivOfIso
    (reesAdicProjectiveIntegerCechObject (R := R) (M := M) (ι := ι) I G d q)
    (reesAdicProjectiveIntegerCechHomologyDirectSumIso (R := R) (M := M) (ι := ι) I G d q)

/-- Rees 単項式の実際の Čech 作用は、直和の第 j 成分を第 i+j 成分へ送る。
原典 Stacks 30.20.1 の Hⁱ の Rees 次数付き作用に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicCechIntegerDirectSum_monomial_smul_lof
    (i j : ℕ) (a : R) (ha : a ∈ I ^ i) (d : ℤ) (q : ℕ)
    (x : (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι)
      (reesAdicProjectivePiece (ι := ι) I G j) d)).homology q) :
    letI := reesAdicCechIntegerDirectSumTransportedModule (R := R) (M := M) (ι := ι) I G d q
    (⟨Polynomial.monomial i a, reesAlgebra.monomial_mem.mpr ha⟩ : reesAlgebra I) •
        DirectSum.lof R ℕ (fun n ↦ (fullCechComplex
          (projectiveNatGradedModuleChartDiagram (ι := ι)
            (reesAdicProjectivePiece (ι := ι) I G n) d)).homology q) j x =
      DirectSum.lof R ℕ (fun n ↦ (fullCechComplex
        (projectiveNatGradedModuleChartDiagram (ι := ι)
          (reesAdicProjectivePiece (ι := ι) I G n) d)).homology q) (i + j)
        (((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
          (fullCechComplexMap (reesAdicProjectiveDegreeShiftChartMap
            (R := R) (M := M) (ι := ι) I G i j a ha d))).hom x) := by
  exact projectiveScalarRestrictionTransportOfIso_component_smul
    (reesAdicProjectiveIntegerCechObject (R := R) (M := M) (ι := ι) I G d q)
    (reesAdicProjectiveIntegerCechHomologyDirectSumIso (R := R) (M := M) (ι := ι) I G d q)
    (reesAdicProjectiveIntegerCechComponentMap (R := R) (M := M) (ι := ι) I G d q j)
    (reesAdicProjectiveIntegerCechComponentMap (R := R) (M := M) (ι := ι) I G d q (i + j))
    (ModuleCat.ofHom (DirectSum.lof R ℕ (fun n ↦ (fullCechComplex
      (projectiveNatGradedModuleChartDiagram (ι := ι)
        (reesAdicProjectivePiece (ι := ι) I G n) d)).homology q) j))
    (ModuleCat.ofHom (DirectSum.lof R ℕ (fun n ↦ (fullCechComplex
      (projectiveNatGradedModuleChartDiagram (ι := ι)
        (reesAdicProjectivePiece (ι := ι) I G n) d)).homology q) (i + j)))
    ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
      (fullCechComplexMap (reesAdicProjectiveDegreeShiftChartMap
        (R := R) (M := M) (ι := ι) I G i j a ha d)))
    (⟨Polynomial.monomial i a, reesAlgebra.monomial_mem.mpr ha⟩ : reesAlgebra I)
    (reesAdicProjectiveIntegerCechComponentMap_directSum (R := R) (M := M) (ι := ι) I G d q j)
    (reesAdicProjectiveIntegerCechComponentMap_directSum
      (R := R) (M := M) (ι := ι) I G d q (i + j))
    (reesAdicProjectiveIntegerCechComponentMap_monomial
      (R := R) (M := M) (ι := ι) I G i j a ha d q) x

/-- コホモロジーの直和の、第 n Rees 次数の部分加群。 -/
def reesAdicCechIntegerDirectSumPiece (d : ℤ) (q n : ℕ) :
    Submodule R (ReesIntegerCechDirectSum (R := R) (M := M) (ι := ι) I G d q) :=
  LinearMap.range (DirectSum.lof R ℕ (fun j ↦ (fullCechComplex
    (projectiveNatGradedModuleChartDiagram (ι := ι)
      (reesAdicProjectivePiece (ι := ι) I G j) d)).homology q) n)

/-- 移した B 作用は、実際の Rees 次数の直和分解と両立する。
原典 Stacks 30.20.1 の Hⁱ の次数付き Rees 作用に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicCechIntegerDirectSumGradedSMul (d : ℤ) (q : ℕ) :
    letI := reesAdicCechIntegerDirectSumTransportedModule (R := R) (M := M) (ι := ι) I G d q
    SetLike.GradedSMul (reesGrade I)
      (reesAdicCechIntegerDirectSumPiece (R := R) (M := M) (ι := ι) I G d q) := by
  letI := reesAdicCechIntegerDirectSumTransportedModule (R := R) (M := M) (ι := ι) I G d q
  refine ⟨?_⟩
  intro i j b x hb hx
  change b • x ∈ reesAdicCechIntegerDirectSumPiece (R := R) (M := M) (ι := ι) I G d q (i + j)
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  let a := b.val.coeff i
  have ha : a ∈ I ^ i := b.property i
  have hba : b = (⟨Polynomial.monomial i a, reesAlgebra.monomial_mem.mpr ha⟩ : reesAlgebra I) :=
    Subtype.ext ((mem_reesGrade_iff I i b).mp hb)
  rw [hba, reesAdicCechIntegerDirectSum_monomial_smul_lof
    (R := R) (M := M) (ι := ι) I G i j a ha d q y]
  exact LinearMap.mem_range.mpr ⟨_, rfl⟩

/-- B 上の整数次数の Rees Čech コホモロジーは B 上有限生成。
原典 Stacks 30.20.1 の Hⁱ の有限性に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveIntegerCechObject_finite [IsNoetherianRing R]
    [Module.Finite (MvPolynomial ι R) M] (d : ℤ) (q : ℕ) :
    Module.Finite (reesAlgebra I)
      (reesAdicProjectiveIntegerCechObject (R := R) (M := M) (ι := ι) I G d q) := by
  let GB := reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G
  letI : DirectSum.Decomposition GB :=
    reesProjectiveGradeDecomposition (S := MvPolynomial ι R) I G
  letI : DirectSum.Decomposition (projectiveNatGradingInt GB) :=
    projectiveNatGradingIntDecomposition GB
  letI : Module.Finite (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
    reesAdicPolynomialModule_finite (ι := ι) I M
  exact projectiveGradedFullCechHomology_finite
    (R := reesAlgebra I) (ι := ι) (M := ReesAdicTotalModule (ι := ι) (M := M) I)
    (projectiveNatGradingInt GB) d q

/-- 次数付き性を確認した Rees 作用について、Čech コホモロジーの直和は B 上有限。
原典 Stacks 30.20.1 の Hⁱ の直和の有限性に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicCechIntegerDirectSumFinite [IsNoetherianRing R]
    [Module.Finite (MvPolynomial ι R) M] (d : ℤ) (q : ℕ) :
    letI := reesAdicCechIntegerDirectSumTransportedModule (R := R) (M := M) (ι := ι) I G d q
    Module.Finite (reesAlgebra I)
      (ReesIntegerCechDirectSum (R := R) (M := M) (ι := ι) I G d q) := by
  letI := reesAdicCechIntegerDirectSumTransportedModule (R := R) (M := M) (ι := ι) I G d q
  letI := reesAdicProjectiveIntegerCechObject_finite (R := R) (M := M) (ι := ι) I G d q
  exact projectiveScalarRestrictionTransportOfIso_finite
    (reesAdicProjectiveIntegerCechObject (R := R) (M := M) (ι := ι) I G d q)
    (reesAdicProjectiveIntegerCechHomologyDirectSumIso (R := R) (M := M) (ι := ι) I G d q)

end SerrePositivity.AlgebraicGeometry
