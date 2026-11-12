module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCoefficientChartTransport
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatPolynomialCoefficientChange
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartMap

/-!
概要：自然数次数の係数変更比較を、次数付き加群の射に自然にする。
方針：整数次数への零延長と係数制限の交換を使い、既存の自然性へ帰着する。
規約：写像は変更後の多項式環上線形とする。
使われ方：閉厚化の係数表示と I 進遷移を同じ Čech 比較で追う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {ι : Type} [DecidableEq ι] [Fintype ι]
local instance projectiveNatCoefficientMapPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι B) :=
  (MvPolynomial.map (algebraMap R B)).toAlgebra
local instance projectiveNatCoefficientMapPolynomialTower :
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
variable (G : ℕ → Submodule B M) (H : ℕ → Submodule B N)
variable [SetLike.GradedSMul
  (MvPolynomial.homogeneousSubmodule ι B) G]
variable [SetLike.GradedSMul
  (MvPolynomial.homogeneousSubmodule ι R)
  (fun d ↦ (G d).restrictScalars R)]
variable [SetLike.GradedSMul
  (MvPolynomial.homogeneousSubmodule ι B) H]
variable [SetLike.GradedSMul
  (MvPolynomial.homogeneousSubmodule ι R)
  (fun d ↦ (H d).restrictScalars R)]
variable (f : M →ₗ[MvPolynomial ι B] N)
variable (hf : ∀ n, ∀ m ∈ G n, f m ∈ H n)


/-- 自然数次数の係数比較を、次数成分の恒等写像を介して構成する。 -/
def projectiveNatCoefficientChartIso (d : ℤ) :
    projectiveNatGradedModuleChartDiagram (ι := ι) (fun n ↦ (G n).restrictScalars R) d ≅
      projectiveNatGradedModuleChartDiagram (R := B) (ι := ι) G d ⋙
        ModuleCat.restrictScalars (algebraMap R B) := by
  let hG : (fun n ↦ (projectiveNatGradingInt G n).restrictScalars R) =
      projectiveNatGradingInt (fun n ↦ (G n).restrictScalars R) :=
    funext (projectiveNatGradingInt_restrictScalars (R := R) G)
  letI := projectiveNatGradingIntSMul (R := B) (ι := ι) G
  letI := projectiveNatGradingIntSMul (R := R) (ι := ι) (fun n ↦ (G n).restrictScalars R)
  exact projectiveCoefficientChartIsoOfRestrictEq (R := R) (B := B) (ι := ι)
    (projectiveNatGradingInt G)
    (projectiveNatGradingInt (fun n ↦ (G n).restrictScalars R)) hG d

/-- 自然数次数の係数比較は、次数を保つ加群の射に自然。 -/
theorem projectiveNatCoefficientChartIso_naturality (d : ℤ) :
    projectiveNatGradedModuleChartMap (ι := ι)
        (fun n ↦ (G n).restrictScalars R) (fun n ↦ (H n).restrictScalars R)
        (f.restrictScalars (MvPolynomial ι R)) hf d ≫
      (projectiveNatCoefficientChartIso (R := R) (ι := ι) H d).hom =
    (projectiveNatCoefficientChartIso (R := R) (ι := ι) G d).hom ≫
      Functor.whiskerRight (projectiveNatGradedModuleChartMap (R := B) (ι := ι) G H f hf d)
        (ModuleCat.restrictScalars (algebraMap R B)) := by
  let hG : (fun n ↦ (projectiveNatGradingInt G n).restrictScalars R) =
      projectiveNatGradingInt (fun n ↦ (G n).restrictScalars R) :=
    funext (projectiveNatGradingInt_restrictScalars (R := R) G)
  let hH : (fun n ↦ (projectiveNatGradingInt H n).restrictScalars R) =
      projectiveNatGradingInt (fun n ↦ (H n).restrictScalars R) :=
    funext (projectiveNatGradingInt_restrictScalars (R := R) H)
  letI := projectiveNatGradingIntSMul (R := B) (ι := ι) G
  letI := projectiveNatGradingIntSMul (R := B) (ι := ι) H
  letI := projectiveNatGradingIntSMul (R := R) (ι := ι) (fun n ↦ (G n).restrictScalars R)
  letI := projectiveNatGradingIntSMul (R := R) (ι := ι) (fun n ↦ (H n).restrictScalars R)
  letI : SetLike.GradedSMul
      (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (fun n ↦ (projectiveNatGradingInt G n).restrictScalars R) := by
    rw [hG]
    exact projectiveNatGradingIntSMul (R := R) (ι := ι) (fun n ↦ (G n).restrictScalars R)
  letI : SetLike.GradedSMul
      (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (fun n ↦ (projectiveNatGradingInt H n).restrictScalars R) := by
    rw [hH]
    exact projectiveNatGradingIntSMul (R := R) (ι := ι) (fun n ↦ (H n).restrictScalars R)
  exact projectiveCoefficientChartIsoOfRestrictEq_naturality
    (R := R) (B := B) (ι := ι)
    (projectiveNatGradingInt G)
    (projectiveNatGradingInt (fun n ↦ (G n).restrictScalars R))
    (projectiveNatGradingInt H)
    (projectiveNatGradingInt (fun n ↦ (H n).restrictScalars R)) hG hH f
    (projectiveNatGradingInt_map_mem G H f hf)
    (projectiveNatGradingInt_map_mem _ _ (f.restrictScalars (MvPolynomial ι R)) hf) d

/-- 自然な標準開比較が誘導する Čech コホモロジーの係数比較。
原典 Stacks 30.20.5 の Hⁱ に対応する Čech 版の自然性に使う。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveNatCoefficientCechIso (d : ℤ) (q : ℕ) :=
  (fullCechComplexFunctor (R := R) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).mapIso
      (projectiveNatCoefficientChartIso (R := R) (B := B) (ι := ι) G d) ≪≫
    projectiveCechRestrictScalarsHomologyIso (algebraMap R B)
      (projectiveNatGradedModuleChartDiagram (R := B) (ι := ι) G d) q

/-- 自然数次数の Čech 係数比較は、次数を保つ加群写像に自然。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる Čech 版の可換式。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveNatCoefficientCechIso_naturality (d : ℤ) (q : ℕ) :
    projectiveNatGradedModuleCechHomologyMap (ι := ι)
        (fun n ↦ (G n).restrictScalars R) (fun n ↦ (H n).restrictScalars R)
        (f.restrictScalars (MvPolynomial ι R)) hf d q ≫
      (projectiveNatCoefficientCechIso (R := R) (ι := ι) H d q).hom =
    (projectiveNatCoefficientCechIso (R := R) (ι := ι) G d q).hom ≫
      (ModuleCat.restrictScalars (algebraMap R B)).map
        (projectiveNatGradedModuleCechHomologyMap (R := B) (ι := ι) G H f hf d q) := by
  let K := fullCechComplexFunctor (R := R) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  let F := ModuleCat.restrictScalars (algebraMap R B)
  let η := projectiveNatGradedModuleChartMap (R := B) (ι := ι) G H f hf d
  have hc := congrArg (fun a ↦ K.map a)
    (projectiveNatCoefficientChartIso_naturality (R := R) (B := B) (ι := ι) G H f hf d)
  simp only [Functor.map_comp] at hc
  have hb : K.map (Functor.whiskerRight η F) ≫
      (projectiveCechRestrictScalarsHomologyIso (algebraMap R B)
        (projectiveNatGradedModuleChartDiagram (R := B) (ι := ι) H d) q).hom =
    (projectiveCechRestrictScalarsHomologyIso (algebraMap R B)
        (projectiveNatGradedModuleChartDiagram (R := B) (ι := ι) G d) q).hom ≫
      F.map (projectiveNatGradedModuleCechHomologyMap (R := B) (ι := ι) G H f hf d q) :=
    projectiveCechRestrictScalarsHomologyIso_naturality (algebraMap R B) η q
  change K.map (projectiveNatGradedModuleChartMap (ι := ι)
      (fun n ↦ (G n).restrictScalars R) (fun n ↦ (H n).restrictScalars R)
      (f.restrictScalars (MvPolynomial ι R)) hf d) ≫
      (K.map (projectiveNatCoefficientChartIso (R := R) (ι := ι) H d).hom ≫
        (projectiveCechRestrictScalarsHomologyIso (algebraMap R B)
          (projectiveNatGradedModuleChartDiagram (R := B) (ι := ι) H d) q).hom) =
    (K.map (projectiveNatCoefficientChartIso (R := R) (ι := ι) G d).hom ≫
        (projectiveCechRestrictScalarsHomologyIso (algebraMap R B)
          (projectiveNatGradedModuleChartDiagram (R := B) (ι := ι) G d) q).hom) ≫
      F.map (projectiveNatGradedModuleCechHomologyMap (R := B) (ι := ι) G H f hf d q)
  rw [← Category.assoc, hc, Category.assoc, hb]
  simp only [Category.assoc]

end SerrePositivity.AlgebraicGeometry
