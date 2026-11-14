module

public import SerrePositivity.AlgebraicGeometry.ProjectiveRingQuotientGrading
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedEquiv
public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveQuotient

/-!
概要：Rees の閉厚化の商加群を、実際の環のイデアルによる商と照合する。
方針：拡大イデアルの作用を基底へ制限し、商の比較を多項式線形同型へ昇格する。
規約：同じ商射影と次数成分を保つ。非平坦な H とテンソル積の交換ではない。
使われ方：閉厚化の Čech Frobenius を既存の形式関数へつなぐ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R)
local instance reesClosedRingSourcePolynomialModule (n : ℕ) :
    Module (MvPolynomial ι R) (reesAdicProjectiveQuotient (ι := ι) (M := A) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) I n
local instance reesClosedRingSourcePolynomialTower (n : ℕ) :
    IsScalarTower R (MvPolynomial ι R)
      (reesAdicProjectiveQuotient (ι := ι) (M := A) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) I n

/-- Rees の閉厚化の部分加群は、A の拡大イデアルの係数制限。 -/
theorem reesClosedRing_submodule_eq (n : ℕ) :
    reesAdicProjectiveSubmodule (ι := ι) (M := A) I n =
      ((I ^ n).map (algebraMap R A)).restrictScalars R := by
  unfold reesAdicProjectiveSubmodule
  rw [reesExtendedAdic_restrictScalars, Ideal.smul_top_eq_map]

/-- Rees の商加群表示と、実際の環の閉厚化との R 線形同型。 -/
def reesClosedRingLinearEquiv (n : ℕ) :
    reesAdicProjectiveQuotient (ι := ι) (M := A) I n ≃ₗ[R]
      A ⧸ (I ^ n).map (algebraMap R A) :=
  (Submodule.quotEquivOfEq _ _ (reesClosedRing_submodule_eq (ι := ι) I n)).trans
    (Submodule.Quotient.restrictScalarsEquiv R ((I ^ n).map (algebraMap R A)))

/-- 環の商との比較は、同じ代表元を持つ商の元を対応させる。 -/
@[simp] theorem reesClosedRingLinearEquiv_mk (n : ℕ) (a : A) :
    reesClosedRingLinearEquiv (ι := ι) I n (Submodule.Quotient.mk a) =
      Ideal.Quotient.mk ((I ^ n).map (algebraMap R A)) a := rfl

/-- 実際の環の商との比較は、元の多項式環の作用も保つ。 -/
def reesClosedRingPolynomialEquiv (n : ℕ) :
    reesAdicProjectiveQuotient (ι := ι) (M := A) I n ≃ₗ[MvPolynomial ι R]
      A ⧸ (I ^ n).map (algebraMap R A) where
  toEquiv := (reesClosedRingLinearEquiv (ι := ι) I n).toEquiv
  map_add' := (reesClosedRingLinearEquiv (ι := ι) I n).map_add
  map_smul' a x := by
    refine Submodule.Quotient.induction_on
      (reesAdicProjectiveSubmodule (ι := ι) (M := A) I n) x (fun m ↦ ?_)
    rfl

/-- 多項式線形な環の商の比較も、同じ代表元を送る。 -/
@[simp] theorem reesClosedRingPolynomialEquiv_mk (n : ℕ) (a : A) :
    reesClosedRingPolynomialEquiv (ι := ι) I n (Submodule.Quotient.mk a) =
      Ideal.Quotient.mk ((I ^ n).map (algebraMap R A)) a := rfl

variable (G : ℕ → Submodule R A) [DirectSum.Decomposition G]

/-- 閉厚化の二つの表示の比較は、各 Proj 次数を両方向で対応させる。 -/
theorem reesClosedRingPolynomialEquiv_mem_iff (n j : ℕ)
    (x : reesAdicProjectiveQuotient (ι := ι) (M := A) I n) :
    reesClosedRingPolynomialEquiv (ι := ι) I n x ∈
        projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G j ↔
      x ∈ reesAdicProjectiveQuotientPiece (ι := ι) I G n j := by
  constructor
  · rintro ⟨a, ha, he⟩
    refine ⟨a, ha, ?_⟩
    apply (reesClosedRingPolynomialEquiv (ι := ι) I n).injective
    exact he
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

variable [DecidableEq ι] [Fintype ι]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
local instance reesClosedRingQuotientGradedSMul (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) I G n) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) I G n

/-- Rees の閉厚化と環の閉厚化の実際の標準開図式の比較。 -/
def reesClosedRingChartIso (n : ℕ) (d : ℤ) :
    projectiveNatGradedModuleChartDiagram (ι := ι)
        (reesAdicProjectiveQuotientPiece (ι := ι) I G n) d ≅
      projectiveNatGradedModuleChartDiagram (ι := ι)
        (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) d :=
  projectiveNatGradedModuleChartIso
    (reesAdicProjectiveQuotientPiece (ι := ι) I G n)
    (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)
    (reesClosedRingPolynomialEquiv (ι := ι) I n)
    (fun j x hx ↦ (reesClosedRingPolynomialEquiv_mem_iff (ι := ι) I G n j x).mpr hx)
    (fun j y hy ↦ (reesClosedRingPolynomialEquiv_mem_iff (ι := ι) I G n j
      ((reesClosedRingPolynomialEquiv (ι := ι) I n).symm y)).mp (by simpa using hy)) d

/-- Rees の閉厚化の Čech H と、実際の環の商の Čech H の比較。
原典 Stacks 30.20.4–30.20.5 と BS17 Lemma 4.6(i) の Hⁱ に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesClosedRingCechIso (n : ℕ) (d : ℤ) (q : ℕ) :
    (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι)
      (reesAdicProjectiveQuotientPiece (ι := ι) I G n) d)).homology q ≅
    (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι)
      (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) d)).homology q :=
  (fullCechComplexFunctor (R := R) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).mapIso
      (reesClosedRingChartIso (ι := ι) I G n d)

end SerrePositivity.AlgebraicGeometry
