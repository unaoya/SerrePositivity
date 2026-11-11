module

public import SerrePositivity.AlgebraicGeometry.ReesIntegerCechAction

/-!
概要：各 IⁿM の Čech コホモロジーを Rees 環上のコホモロジーへ送り、作用を追う。
方針：整数次数の包含と係数比較を合成し、単項式の可換式をコホモロジーへ写す。
規約：B 上のコホモロジーを R へ制限した対象への写像を使う。
使われ方：直和の比較で移した B 作用が Rees 次数を保つことの確認。
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

local instance reesIntegerComponentCechPieceAddGroup (n : ℕ) : AddCommGroup
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).addCommGroup
local instance reesIntegerComponentCechPieceSMul (n : ℕ) : SMul R
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).module.toSMul
local instance reesIntegerComponentCechPieceModule (n : ℕ) : Module R
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n).module
local instance reesIntegerComponentCechPiecePolynomialModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
local instance reesIntegerComponentCechPieceTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance reesIntegerComponentCechTotalSMul : SMul R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesAdicTotalBaseModule (ι := ι) (M := M) I).toSMul
local instance reesIntegerComponentCechTotalModule : Module R (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule (ι := ι) (M := M) I
local instance reesIntegerComponentCechPolynomialTower : IsScalarTower R (MvPolynomial ι R)
    (ReesAdicTotalModule (ι := ι) (M := M) I) := IsScalarTower.of_compHom _ _ _
local instance reesIntegerComponentCechTotalReesSMul : SMul (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  (reesExtendedModule (S := MvPolynomial ι R) (M := M) I).toSMul
local instance reesIntegerComponentCechTotalReesModule : Module (reesAlgebra I) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesExtendedModule (S := MvPolynomial ι R) (M := M) I
local instance reesIntegerComponentCechTotalReesTower : IsScalarTower R (reesAlgebra I)
    (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesAdicTotalBaseModule_scalarTower (ι := ι) (M := M) I

local instance reesIntegerComponentCechPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I)) :=
  reesPolynomialCoefficientAlgebra (ι := ι) I
local instance reesIntegerComponentCechRingTower :
    IsScalarTower R (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I)) :=
  reesPolynomialCoefficientAlgebra_scalarTower (ι := ι) I
local instance reesIntegerComponentCechModule :
    Module (MvPolynomial ι (reesAlgebra I)) (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  Module.compHom _ (reesPolynomialBaseChange (ι := ι) I)
local instance reesIntegerComponentCechSourceTower :
    IsScalarTower (MvPolynomial ι R) (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_source_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesIntegerComponentCechBaseTower :
    IsScalarTower R (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_base_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesIntegerComponentCechReesTower :
    IsScalarTower (reesAlgebra I) (MvPolynomial ι (reesAlgebra I))
      (ReesAdicTotalModule (ι := ι) (M := M) I) :=
  reesPolynomialBaseChange_module_scalarTower (ι := ι) I
    (ReesAdicTotalModule (ι := ι) (M := M) I)
local instance reesIntegerComponentCechBaseGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (fun n ↦ (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G n).restrictScalars R) :=
  reesAdicProjectiveBaseGradedSMul (R := R) (M := M) (ι := ι) I G
local instance reesIntegerComponentCechReesGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι (reesAlgebra I))
      (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G) :=
  reesProjectivePolynomialGradedSMul (R := R) (M := M) (ι := ι) I G

local instance reesIntegerComponentCechPieceNatGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectivePiece (ι := ι) I G n) :=
  reesAdicProjectivePieceGradedSMul (ι := ι) I G n
local instance reesIntegerComponentCechPieceIntGraded (n : ℕ) :
    SetLike.GradedSMul (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt (reesAdicProjectivePiece (ι := ι) I G n)) :=
  projectiveNatGradingIntSMul (ι := ι) (reesAdicProjectivePiece (ι := ι) I G n)
local instance reesIntegerComponentCechIntReesGraded :
    SetLike.GradedSMul
      (AddMonoidAlgebra.gradeBy (reesAlgebra I) (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt
        (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G)) :=
  projectiveNatGradingIntSMul (R := reesAlgebra I) (ι := ι)
    (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G)
local instance reesIntegerComponentCechIntBaseGraded :
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

/-- B 上で整数次数へ延ばした Rees の標準開 Čech コホモロジー。
原典 Stacks 30.20.1 の Hⁱ に対応する Čech 版の対象。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesAdicProjectiveIntegerCechObject (d : ℤ) (q : ℕ) : ModuleCat.{u} (reesAlgebra I) :=
  (fullCechComplex (projectiveGradedModuleChartDiagram
    (R := reesAlgebra I) (ι := ι) (projectiveNatGradingInt
      (reesProjectiveGrade (R := R) (M := M) (S := MvPolynomial ι R) I G)) d)).homology q

/-- 各 IⁿM の Čech コホモロジーから、Rees の B 上の計算を R に制限したものへの写像。
原典 Stacks 30.20.1 の Hⁱ の直和比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesAdicProjectiveIntegerCechComponentMap (d : ℤ) (q n : ℕ) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
    (fullCechComplexMap
      (reesAdicProjectiveIntegerChartInclusion (R := R) (M := M) (ι := ι) I G d n)) ≫
    (reesAdicProjectiveIntegerCoefficientCechHomologyIso
      (R := R) (M := M) (ι := ι) I G d q).hom

/-- Rees の各次数のコホモロジーからの写像は、直和比較で lof に移る。
原典 Stacks 30.20.1 の Hⁱ の直和比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveIntegerCechComponentMap_directSum (d : ℤ) (q n : ℕ) :
    reesAdicProjectiveIntegerCechComponentMap (R := R) (M := M) (ι := ι) I G d q n ≫
      (reesAdicProjectiveIntegerCechHomologyDirectSumIso
        (R := R) (M := M) (ι := ι) I G d q).hom =
    ModuleCat.ofHom (DirectSum.lof R ℕ
      (fun j ↦ (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι)
        (reesAdicProjectivePiece (ι := ι) I G j) d)).homology q) n) := by
  simp only [reesAdicProjectiveIntegerCechComponentMap,
    reesAdicProjectiveIntegerCechHomologyDirectSumIso,
    reesAdicProjectiveIntegerCoefficientCechHomologyIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact reesAdicProjectiveIntegerBaseCechHomologyDirectSumIso_inclusion
    (R := R) (M := M) (ι := ι) I G d q n

/-- Rees 単項式は、各次数からの Čech 写像を次の次数からの写像へ移す。
原典 Stacks 30.20.1 の Hⁱ の Rees 作用に対応する Čech 版の可換式。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveIntegerCechComponentMap_monomial
    (i j : ℕ) (a : R) (ha : a ∈ I ^ i) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveIntegerCechComponentMap (R := R) (M := M) (ι := ι) I G d q j ≫
      (ModuleCat.restrictScalars (algebraMap R (reesAlgebra I))).map
        ((⟨Polynomial.monomial i a, reesAlgebra.monomial_mem.mpr ha⟩ : reesAlgebra I) •
          𝟙 (reesAdicProjectiveIntegerCechObject (R := R) (M := M) (ι := ι) I G d q)) =
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
        (fullCechComplexMap
          (reesAdicProjectiveDegreeShiftChartMap (R := R) (M := M) (ι := ι) I G i j a ha d)) ≫
      reesAdicProjectiveIntegerCechComponentMap (R := R) (M := M) (ι := ι) I G d q (i + j) := by
  let K := fullCechComplexFunctor (R := R) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  let b : reesAlgebra I := ⟨Polynomial.monomial i a, reesAlgebra.monomial_mem.mpr ha⟩
  have hm := congrArg (fun f ↦ K.map f)
    (reesAdicProjectiveIntegerChartInclusion_monomial (R := R) (M := M) (ι := ι) I G i j a ha d)
  simp only [Functor.map_comp] at hm
  dsimp only [K, Functor.comp_map, fullCechComplexFunctor] at hm
  have hs := reesAdicProjectiveIntegerCoefficientCechHomologyIso_scalar
    (R := R) (M := M) (ι := ι) I G b d q
  dsimp only [reesAdicProjectiveIntegerCechComponentMap, reesAdicProjectiveIntegerCechObject]
  rw [Category.assoc, ← hs, ← Category.assoc, hm, Category.assoc]

end SerrePositivity.AlgebraicGeometry
