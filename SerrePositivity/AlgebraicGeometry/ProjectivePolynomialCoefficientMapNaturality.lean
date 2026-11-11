module

public import SerrePositivity.AlgebraicGeometry.ProjectivePolynomialCoefficientChange
public import SerrePositivity.AlgebraicGeometry.ProjectiveScalarGradedMapNaturality
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechRestrictScalarsNaturality
public import Mathlib.CategoryTheory.Whiskering

/-!
概要：多項式の係数環を変える標準開の比較は、次数を保つ加群写像に自然。
方針：各標準開で局所化の自然性と係数制限の自然性を合成する。
規約：写像は変更後の多項式環上線形とし、変更前の環へ線形性を制限する。
使われ方：Rees 係数の作用を、二つの係数環上の Čech 計算で照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory

universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {ι : Type} [DecidableEq ι] [Fintype ι]
local instance projectiveCoefficientMapPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι B) :=
  (MvPolynomial.map (algebraMap R B)).toAlgebra
local instance projectiveCoefficientMapPolynomialTower :
    IsScalarTower R (MvPolynomial ι R) (MvPolynomial ι B) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change MvPolynomial.C (algebraMap R B r) =
    MvPolynomial.map (algebraMap R B) (MvPolynomial.C r)
  rw [MvPolynomial.map_C]

variable {M N : Type u} [AddCommGroup M] [Module R M] [Module B M]
variable [Module (MvPolynomial ι R) M] [Module (MvPolynomial ι B) M]
variable [IsScalarTower R B M] [IsScalarTower R (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι B) M] [IsScalarTower B (MvPolynomial ι B) M]
variable [IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B) M]
variable [AddCommGroup N] [Module R N] [Module B N]
variable [Module (MvPolynomial ι R) N] [Module (MvPolynomial ι B) N]
variable [IsScalarTower R B N] [IsScalarTower R (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι B) N] [IsScalarTower B (MvPolynomial ι B) N]
variable [IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B) N]
variable (G : ℤ → Submodule B M) (H : ℤ → Submodule B N)
variable [SetLike.GradedSMul
  (AddMonoidAlgebra.gradeBy B (projectivePolynomialDegree (ι := ι))) G]
variable [SetLike.GradedSMul
  (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
  (fun d ↦ (G d).restrictScalars R)]
variable [SetLike.GradedSMul
  (AddMonoidAlgebra.gradeBy B (projectivePolynomialDegree (ι := ι))) H]
variable [SetLike.GradedSMul
  (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
  (fun d ↦ (H d).restrictScalars R)]
variable (f : M →ₗ[MvPolynomial ι B] N)
variable (hf : ∀ n, ∀ m ∈ G n, f m ∈ H n)

/-- 各標準開の係数環比較は、Proj 次数を保つ加群写像に自然。 -/
theorem projectiveGradedPolynomialCoefficientChangeLinearEquiv_map
    (T : Finset ι) (d : ℤ)
    (z : (projectiveGradedModuleChartDiagram (ι := ι)
      (fun n ↦ (G n).restrictScalars R) d).obj T) :
    projectiveGradedPolynomialCoefficientChangeLinearEquiv (R := R) (ι := ι) H T d
        (((projectiveGradedModuleChartMap (ι := ι)
          (fun n ↦ (G n).restrictScalars R) (fun n ↦ (H n).restrictScalars R)
          d (f.restrictScalars (MvPolynomial ι R)) hf).app T).hom z) =
      ((projectiveGradedModuleChartMap (R := B) (ι := ι) G H d f hf).app T).hom
        (projectiveGradedPolynomialCoefficientChangeLinearEquiv (R := R) (ι := ι) G T d z) := by
  change projectiveGradedPolynomialCoefficientChangeLinearEquiv (R := R) (ι := ι) H T d
      (projectiveGradedAwayMap (projectiveLaurentDenominator R T)
        (fun k ↦ (G (d + k • (T.card : ℤ))).restrictScalars R)
        (fun k ↦ (H (d + k • (T.card : ℤ))).restrictScalars R)
        (f.restrictScalars (MvPolynomial ι R)) (fun k ↦ hf _) z) = _
  simp only [projectiveGradedPolynomialCoefficientChangeLinearEquiv, LinearEquiv.trans_apply]
  rw [projectiveModuleScalarGradedAwayLinearEquivOfEq_map
    (R := R) (projectiveLaurentDenominator R T) (projectiveLaurentDenominator B T)
    (projectivePolynomialCoefficientDenominator (R := R) (B := B) T)
    (fun k ↦ (G (d + k • (T.card : ℤ))).restrictScalars R)
    (fun k ↦ (H (d + k • (T.card : ℤ))).restrictScalars R) f
    (fun k ↦ hf _) (projectiveGradedChart_mul_denominator
      (R := R) (ι := ι) (fun n ↦ (G n).restrictScalars R) T d)]
  exact projectiveGradedAwayScalarRestrictionLinearEquiv_map (R := R)
    (projectiveLaurentDenominator B T)
    (fun k ↦ G (d + k • (T.card : ℤ))) (fun k ↦ H (d + k • (T.card : ℤ))) f
    (fun k ↦ hf _) _

/-- 係数環比較の図式の同型は、Proj 次数を保つ加群写像に自然。 -/
theorem projectiveGradedPolynomialCoefficientChangeChartIso_naturality (d : ℤ) :
    projectiveGradedModuleChartMap (ι := ι)
        (fun n ↦ (G n).restrictScalars R) (fun n ↦ (H n).restrictScalars R)
        d (f.restrictScalars (MvPolynomial ι R)) hf ≫
      (projectiveGradedPolynomialCoefficientChangeChartIso (R := R) (ι := ι) H d).hom =
    (projectiveGradedPolynomialCoefficientChangeChartIso (R := R) (ι := ι) G d).hom ≫
      Functor.whiskerRight (projectiveGradedModuleChartMap (R := B) (ι := ι) G H d f hf)
        (ModuleCat.restrictScalars (algebraMap R B)) := by
  apply NatTrans.ext
  funext T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact projectiveGradedPolynomialCoefficientChangeLinearEquiv_map G H f hf T d z

/-- 多項式係数変更の Čech コホモロジー比較は、次数を保つ写像に自然。
原典 Stacks 30.20.1 の Hⁱ の直和に対する作用に対応する Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveGradedPolynomialCoefficientChangeCechHomologyIso_naturality
    (d : ℤ) (q : ℕ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
        (fullCechComplexMap (projectiveGradedModuleChartMap (ι := ι)
          (fun n ↦ (G n).restrictScalars R) (fun n ↦ (H n).restrictScalars R)
          d (f.restrictScalars (MvPolynomial ι R)) hf)) ≫
      (projectiveGradedPolynomialCoefficientChangeCechHomologyIso
        (R := R) (ι := ι) H d q).hom =
    (projectiveGradedPolynomialCoefficientChangeCechHomologyIso
        (R := R) (ι := ι) G d q).hom ≫
      (ModuleCat.restrictScalars (algebraMap R B)).map
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℕ) q).map
          (fullCechComplexMap
            (projectiveGradedModuleChartMap (R := B) (ι := ι) G H d f hf))) := by
  let C := fullCechComplexFunctor (R := R) (ι := ι)
  let HR := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  let K := C ⋙ HR
  let F := ModuleCat.restrictScalars (algebraMap R B)
  let η := projectiveGradedModuleChartMap (R := B) (ι := ι) G H d f hf
  have hc := congrArg (fun a ↦ K.map a)
    (projectiveGradedPolynomialCoefficientChangeChartIso_naturality G H f hf d)
  simp only [Functor.map_comp] at hc
  have hb := projectiveCechRestrictScalarsHomologyIso_naturality
    (algebraMap R B) η q
  change K.map (projectiveGradedModuleChartMap (ι := ι)
      (fun n ↦ (G n).restrictScalars R) (fun n ↦ (H n).restrictScalars R)
      d (f.restrictScalars (MvPolynomial ι R)) hf) ≫
      (K.map (projectiveGradedPolynomialCoefficientChangeChartIso
        (R := R) (ι := ι) H d).hom ≫
        (projectiveCechRestrictScalarsHomologyIso (algebraMap R B)
          (projectiveGradedModuleChartDiagram (R := B) (ι := ι) H d) q).hom) =
    (K.map (projectiveGradedPolynomialCoefficientChangeChartIso
        (R := R) (ι := ι) G d).hom ≫
        (projectiveCechRestrictScalarsHomologyIso (algebraMap R B)
          (projectiveGradedModuleChartDiagram (R := B) (ι := ι) G d) q).hom) ≫
      F.map ((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℕ) q).map
        (fullCechComplexMap η))
  have hb' : K.map (Functor.whiskerRight η F) ≫
      (projectiveCechRestrictScalarsHomologyIso (algebraMap R B)
        (projectiveGradedModuleChartDiagram (R := B) (ι := ι) H d) q).hom =
    (projectiveCechRestrictScalarsHomologyIso (algebraMap R B)
        (projectiveGradedModuleChartDiagram (R := B) (ι := ι) G d) q).hom ≫
      F.map ((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℕ) q).map
        (fullCechComplexMap η)) := hb
  rw [← Category.assoc, hc, Category.assoc, hb']
  simp only [Category.assoc]

end SerrePositivity.AlgebraicGeometry
