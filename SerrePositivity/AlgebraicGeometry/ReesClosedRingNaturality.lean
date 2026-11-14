module

public import SerrePositivity.AlgebraicGeometry.ReesClosedRingComparison
public import SerrePositivity.AlgebraicGeometry.ReesClosedCechTransition

/-!
概要：環の商との比較を、閉厚化への射影と厚化間の遷移に自然にする。
方針：多項式線形写像の同じ代表元の計算を、標準開と Čech H へ送る。
規約：遷移は既存の Rees の商写像と実際の環の商の因子写像。
使われ方：閉厚化の Frobenius と形式関数の同型の整合性。
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
local instance reesClosedRingNaturalPolynomialModule (n : ℕ) :
    Module (MvPolynomial ι R) (reesAdicProjectiveQuotient (ι := ι) (M := A) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) I n
local instance reesClosedRingNaturalPolynomialTower (n : ℕ) :
    IsScalarTower R (MvPolynomial ι R)
      (reesAdicProjectiveQuotient (ι := ι) (M := A) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) I n

/-- 環の商の比較は、既存の Rees の商への射影を実際の環の射影へ送る。 -/
theorem reesClosedRingPolynomialEquiv_projection (n : ℕ) :
    (reesClosedRingPolynomialEquiv (ι := ι) (A := A) I n).toLinearMap.comp
        (reesAdicProjectiveQuotientProjection (ι := ι) (M := A) I n) =
      (Ideal.Quotient.mkₐ (MvPolynomial ι R) ((I ^ n).map (algebraMap R A))).toLinearMap := by
  apply LinearMap.ext
  intro a
  rfl

/-- 実際の環の閉厚化の間の遷移。係数の指数が下がる商射。 -/
def reesClosedRingTransition (i j : ℕ) (h : j ≤ i) :
    A ⧸ (I ^ i).map (algebraMap R A) →ₐ[MvPolynomial ι R]
      A ⧸ (I ^ j).map (algebraMap R A) :=
  Ideal.Quotient.factorₐ (MvPolynomial ι R)
    (Ideal.map_mono (Ideal.pow_le_pow_right h))

/-- 環の商の遷移は、同じ代表元を送る。 -/
@[simp] theorem reesClosedRingTransition_mk (i j : ℕ) (h : j ≤ i) (a : A) :
    reesClosedRingTransition (ι := ι) I i j h
        (Ideal.Quotient.mk ((I ^ i).map (algebraMap R A)) a) =
      Ideal.Quotient.mk ((I ^ j).map (algebraMap R A)) a := rfl

/-- Rees と環の商の比較は、厚化間の実際の遷移と可換。 -/
theorem reesClosedRingPolynomialEquiv_transition (i j : ℕ) (h : j ≤ i)
    (x : reesAdicProjectiveQuotient (ι := ι) (M := A) I i) :
    reesClosedRingPolynomialEquiv (ι := ι) I j
        (reesAdicProjectiveQuotientTransition (ι := ι) I i j h x) =
      reesClosedRingTransition (ι := ι) I i j h
        (reesClosedRingPolynomialEquiv (ι := ι) I i x) := by
  refine Submodule.Quotient.induction_on
    (reesAdicProjectiveSubmodule (ι := ι) (M := A) I i) x (fun a ↦ ?_)
  rfl

variable (G : ℕ → Submodule R A) [DirectSum.Decomposition G]

/-- 環の閉厚化の遷移も、商の Proj 次数を保つ。 -/
theorem reesClosedRingTransition_preservesPiece (i j : ℕ) (h : j ≤ i)
    (k : ℕ) (x : A ⧸ (I ^ i).map (algebraMap R A))
    (hx : x ∈ projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G k) :
    reesClosedRingTransition (ι := ι) I i j h x ∈
      projectiveRingQuotientGrade ((I ^ j).map (algebraMap R A)) G k := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, ha, rfl⟩

variable [LinearOrder ι] [Fintype ι]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
local instance reesClosedRingNaturalQuotientGradedSMul (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) I G n) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) I G n

/-- 環の閉厚化への射影が誘導する実際の標準開図式の射。 -/
def reesClosedRingProjectionChartMap (n : ℕ) (d : ℤ) :=
  projectiveNatGradedModuleChartMap G
    (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G)
    (Ideal.Quotient.mkₐ (MvPolynomial ι R) ((I ^ n).map (algebraMap R A))).toLinearMap
    (projectiveRingQuotientProjection_preservesPiece (ι := ι) _ G) d

/-- 環の閉厚化の遷移が誘導する実際の標準開図式の射。 -/
def reesClosedRingTransitionChartMap (i j : ℕ) (h : j ≤ i) (d : ℤ) :=
  projectiveNatGradedModuleChartMap
    (projectiveRingQuotientGrade ((I ^ i).map (algebraMap R A)) G)
    (projectiveRingQuotientGrade ((I ^ j).map (algebraMap R A)) G)
    (reesClosedRingTransition (ι := ι) I i j h).toLinearMap
    (reesClosedRingTransition_preservesPiece (ι := ι) I G i j h) d

/-- 実際の標準開の環の商の比較は、既存の閉厚化への射影と可換。 -/
theorem reesClosedRingChartIso_projection (n : ℕ) (d : ℤ) :
    reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n d ≫
        (reesClosedRingChartIso (ι := ι) I G n d).hom =
      reesClosedRingProjectionChartMap (ι := ι) I G n d := by
  simp only [reesAdicProjectiveClosedCechProjectionChartMap, reesClosedRingChartIso,
    projectiveNatGradedModuleChartIso, reesClosedRingProjectionChartMap]
  rw [projectiveNatGradedModuleChartMap_comp]
  congr 1

/-- 環の商の標準開の比較は、以前の閉厚化間の遷移と可換。 -/
theorem reesClosedRingChartIso_transition (i j : ℕ) (h : j ≤ i) (d : ℤ) :
    reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I G i j h d ≫
        (reesClosedRingChartIso (ι := ι) I G j d).hom =
      (reesClosedRingChartIso (ι := ι) I G i d).hom ≫
        reesClosedRingTransitionChartMap (ι := ι) I G i j h d := by
  simp only [reesAdicProjectiveClosedCechTransitionChartMap, reesClosedRingChartIso,
    projectiveNatGradedModuleChartIso, reesClosedRingTransitionChartMap]
  rw [projectiveNatGradedModuleChartMap_comp, projectiveNatGradedModuleChartMap_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact reesClosedRingPolynomialEquiv_transition (ι := ι) I i j h x

/-- 環の商の Čech 比較は、以前の実際の閉厚化への射影と可換。
原典 Stacks 30.20.4–30.20.5 の Hⁱ に使う Čech 版の自然性。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedRingCechIso_projection (n : ℕ) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechProjection (ι := ι) I G n d q ≫
        (reesClosedRingCechIso (ι := ι) I G n d q).hom =
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
        (fullCechComplexMap (reesClosedRingProjectionChartMap (ι := ι) I G n d)) := by
  let H : (Finset ι ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R := fullCechComplexFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  change H.map (reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n d) ≫
      H.map (reesClosedRingChartIso (ι := ι) I G n d).hom =
    H.map (reesClosedRingProjectionChartMap (ι := ι) I G n d)
  rw [← H.map_comp, reesClosedRingChartIso_projection]

/-- 環の商の Čech 比較は、既存の閉厚化の I 進遷移と可換。
原典 Stacks 30.20.4–30.20.5 の Hⁱ に使う Čech 版の自然性。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedRingCechIso_transition (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h d q ≫
        (reesClosedRingCechIso (ι := ι) I G j d q).hom =
      (reesClosedRingCechIso (ι := ι) I G i d q).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
          (fullCechComplexMap (reesClosedRingTransitionChartMap (ι := ι) I G i j h d)) := by
  let H : (Finset ι ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R := fullCechComplexFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  change H.map (reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I G i j h d) ≫
      H.map (reesClosedRingChartIso (ι := ι) I G j d).hom =
    H.map (reesClosedRingChartIso (ι := ι) I G i d).hom ≫
      H.map (reesClosedRingTransitionChartMap (ι := ι) I G i j h d)
  rw [← H.map_comp, ← H.map_comp, reesClosedRingChartIso_transition]

end SerrePositivity.AlgebraicGeometry
