module

public import SerrePositivity.AlgebraicGeometry.ProjectiveScalarGradedLocalization
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedFiniteness
public import SerrePositivity.AlgebraicGeometry.ProjStandardOpen

/-!
概要：多項式加群の標準開係数図式を、斉次代数の次数零局所化の図式へ移す。
方針：自然数次数への制限、係数環の変更、斉次局所化との比較を順につなぐ。
規約：標準開は次数一の変数の像で指定する。
使われ方：射影 Čech 有限性を Proj の標準開の切断に渡す。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory

universe u v

variable {R : Type u} {ι : Type v} {S : Type (max u v)}
variable [CommRing R] [CommRing S] [LinearOrder ι] [Fintype ι]
variable [Algebra R S] [Algebra (MvPolynomial ι R) S]
variable [IsScalarTower R (MvPolynomial ι R) S]
variable (G : ℕ → Submodule R S) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance (f : S) : Module R (HomogeneousLocalization.Away G f) :=
  projectiveHomogeneousAwayModule G f

/-- 多項式の変数の像は斉次代数の次数一の元。 -/
theorem projectivePolynomialVariableImage_mem (i : ι) :
    algebraMap (MvPolynomial ι R) S (MvPolynomial.X i) ∈ G 1 := by
  have hX : MvPolynomial.X i ∈ MvPolynomial.homogeneousSubmodule ι R 1 :=
    MvPolynomial.isHomogeneous_X R i
  have h := SetLike.GradedSMul.smul_mem hX (SetLike.one_mem_graded G)
  simpa only [Algebra.smul_def, mul_one, vadd_eq_add, add_zero, RingHom.id_apply] using h

/-- チャートの分母を斉次代数へ写すと、対応する標準開の元の積になる。 -/
theorem projectivePolynomialDenominatorImage (T : Finset ι) :
    algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T) =
      ∏ i ∈ T, algebraMap (MvPolynomial ι R) S (MvPolynomial.X i) := by
  simp only [projectiveLaurentDenominator, map_prod]

/-- チャートの分母の像の次数は、チャートの添字集合の濃度。 -/
theorem projectivePolynomialDenominatorImage_mem (T : Finset ι) :
    algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T) ∈ G T.card := by
  rw [projectivePolynomialDenominatorImage]
  exact projStandardProduct_degree G _ T (projectivePolynomialVariableImage_mem G)

/-- 整数次数零のチャートを、斉次代数の次数零局所化と線形同一視する。 -/
def projectiveHomogeneousChartLinearEquiv (T : Finset ι) :
    (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).obj T ≃ₗ[R]
      HomogeneousLocalization.Away G
        (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T)) := by
  let V (n : ℕ) := projectiveNatGradingInt G (0 + n • (T.card : ℤ))
  let W (n : ℕ) := G (n • T.card)
  have hVW : V = W := by
    funext n
    have hd : (0 : ℤ) + n • (T.card : ℤ) = ((n • T.card : ℕ) : ℤ) := by
      simp [nsmul_eq_mul]
    exact (congrArg (projectiveNatGradingInt G) hd).trans
      (projectiveNatGradingInt_natCast G (n • T.card))
  let eV := LinearEquiv.ofEq
    (projectiveGradedAway (projectiveLaurentDenominator R T) V)
    (projectiveGradedAway (projectiveLaurentDenominator R T) W)
    (congrArg (projectiveGradedAway (projectiveLaurentDenominator R T)) hVW)
  exact eV.trans ((projectiveScalarGradedAwayLinearEquiv
    (projectiveLaurentDenominator R T) W).trans
      (projectiveHomogeneousAwayLinearEquiv G
        (projectivePolynomialDenominatorImage_mem G T)).symm)

/-- 次数零の斉次局所化を、標準開の局所化加群の制限に沿う係数図式にする。 -/
def projectiveHomogeneousChartDiagram : Finset ι ⥤ ModuleCat R where
  obj T := ModuleCat.of R (HomogeneousLocalization.Away G
    (algebraMap (MvPolynomial ι R) S (projectiveLaurentDenominator R T)))
  map {T U} h := (projectiveHomogeneousChartLinearEquiv G T).toModuleIso.inv ≫
    (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).map h ≫
      (projectiveHomogeneousChartLinearEquiv G U).toModuleIso.hom
  map_id T := by
    rw [(projectiveNatGradedModuleChartDiagram (ι := ι) G 0).map_id, Category.id_comp]
    exact (projectiveHomogeneousChartLinearEquiv (ι := ι) G T).toModuleIso.inv_hom_id
  map_comp {T U V} f g := by
    simp only [CategoryTheory.Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- 標準開の多項式加群の図式と、次数零の斉次局所化の図式の自然同型。 -/
def projectiveHomogeneousChartDiagramIso :
    projectiveNatGradedModuleChartDiagram (ι := ι) G 0 ≅ projectiveHomogeneousChartDiagram (ι := ι) G :=
  NatIso.ofComponents (fun T ↦ (projectiveHomogeneousChartLinearEquiv G T).toModuleIso)
    (by
      intro T U h
      change (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).map h ≫
          (projectiveHomogeneousChartLinearEquiv (ι := ι) G U).toModuleIso.hom =
        (projectiveHomogeneousChartLinearEquiv (ι := ι) G T).toModuleIso.hom ≫
          (projectiveHomogeneousChartLinearEquiv (ι := ι) G T).toModuleIso.inv ≫
            (projectiveNatGradedModuleChartDiagram (ι := ι) G 0).map h ≫
              (projectiveHomogeneousChartLinearEquiv (ι := ι) G U).toModuleIso.hom
      rw [Iso.hom_inv_id_assoc])

/-- 有限生成斉次代数の次数零の標準開 Čech コホモロジーは有限生成。
これは Stacks 30.19.2 の Hⁱ の有限性に対応する射影 Čech 版の補題。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveHomogeneousChartFullCechHomology_finite
    [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) S] (q : ℕ) :
    Module.Finite R ((fullCechComplex (projectiveHomogeneousChartDiagram (ι := ι) G)).homology q) := by
  let D := projectiveNatGradedModuleChartDiagram (ι := ι) G 0
  let E := projectiveHomogeneousChartDiagram (ι := ι) G
  let eComplex : fullCechComplex D ≅ fullCechComplex E :=
    (fullCechComplexFunctor (R := R) (ι := ι)).mapIso (projectiveHomogeneousChartDiagramIso (ι := ι) G)
  let eHomology :=
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) q).mapIso eComplex
  letI : Module.Finite R
      ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) q).obj
        (fullCechComplex D)) := by
    change Module.Finite R ((fullCechComplex D).homology q)
    exact projectiveNatGradedFullCechHomology_finite (ι := ι) G 0 q
  exact Module.Finite.of_surjective eHomology.hom.hom
    ((ModuleCat.epi_iff_surjective eHomology.hom).mp inferInstance)

end SerrePositivity.AlgebraicGeometry
