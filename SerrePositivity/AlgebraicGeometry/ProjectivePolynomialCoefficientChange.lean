module

public import SerrePositivity.AlgebraicGeometry.ProjectiveModuleScalarLocalizationRestriction
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedScalarRestriction
public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChart
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechRestrictScalars
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
概要：二つの係数環上の多項式加群の標準開を、共通の基底環上で比較する。
方針：分母の積の像を同定し、局所化する環の変更と線形構造の係数制限を合成する。
規約：同じ加群の二つの多項式作用と、次数を持つ部分加群の族を入力する。
使われ方：原典 Stacks 30.20.1 の Hⁱ に対応する Čech 版の Rees 比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory

universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {ι : Type} [DecidableEq ι] [Fintype ι]

local instance projectiveCoefficientPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι B) :=
  (MvPolynomial.map (algebraMap R B)).toAlgebra

local instance projectiveCoefficientPolynomialTower :
    IsScalarTower R (MvPolynomial ι R) (MvPolynomial ι B) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change MvPolynomial.C (algebraMap R B r) =
    MvPolynomial.map (algebraMap R B) (MvPolynomial.C r)
  rw [MvPolynomial.map_C]

/-- 多項式の係数変更は、標準開の変数の積を同じ変数の積へ写す。 -/
theorem projectivePolynomialCoefficientDenominator (T : Finset ι) :
    algebraMap (MvPolynomial ι R) (MvPolynomial ι B) (projectiveLaurentDenominator R T) =
      projectiveLaurentDenominator B T := by
  change MvPolynomial.map (algebraMap R B) (projectiveLaurentDenominator R T) = _
  simp only [projectiveLaurentDenominator, map_prod, MvPolynomial.map_X]

variable {N : Type u} [AddCommGroup N] [Module R N] [Module B N]
variable [Module (MvPolynomial ι R) N] [Module (MvPolynomial ι B) N]
variable [IsScalarTower R B N] [IsScalarTower R (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι B) N] [IsScalarTower B (MvPolynomial ι B) N]
variable [IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B) N]
variable (H : ℤ → Submodule B N)

/-- 標準開の係数変更と、B 加群から R 加群への係数制限を合成する。 -/
def projectiveGradedPolynomialCoefficientChangeLinearEquiv (T : Finset ι) (d : ℤ) :=
  (projectiveModuleScalarGradedAwayLinearEquivOfEq
    (R := R) (P := MvPolynomial ι R) (Q := MvPolynomial ι B) (M := N)
    (projectiveLaurentDenominator R T) (projectiveLaurentDenominator B T)
    (projectivePolynomialCoefficientDenominator (R := R) (B := B) T)
    (fun k ↦ (H (d + k • (T.card : ℤ))).restrictScalars R)).trans
      (projectiveGradedAwayScalarRestrictionLinearEquiv
        (R := R) (B := B) (Q := MvPolynomial ι B) (N := N)
        (projectiveLaurentDenominator B T) (fun k ↦ H (d + k • (T.card : ℤ))))

variable [SetLike.GradedSMul
  (AddMonoidAlgebra.gradeBy B (projectivePolynomialDegree (ι := ι))) H]
variable [SetLike.GradedSMul
  (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
  (fun d ↦ (H d).restrictScalars R)]

/-- 多項式の係数変更と係数制限による、標準開の係数図式の同型。 -/
def projectiveGradedPolynomialCoefficientChangeChartIso (d : ℤ) :
    projectiveGradedModuleChartDiagram (ι := ι) (fun n ↦ (H n).restrictScalars R) d ≅
      projectiveGradedModuleChartDiagram (R := B) (M := N) (ι := ι) H d ⋙ ModuleCat.restrictScalars (algebraMap R B) :=
  NatIso.ofComponents (fun T ↦
    (projectiveGradedPolynomialCoefficientChangeLinearEquiv (R := R) (ι := ι) H T d).toModuleIso) (by
    intro T U h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    have hQmem (k : ℕ)
        (m : (H (d + k • (T.card : ℤ))).restrictScalars R) :
        projectiveLaurentDenominator B (U \ T) ^ k • m.val ∈
          (H (d + k • (U.card : ℤ))).restrictScalars R :=
      projectiveGradedChart_mul_mem (R := B) (M := N) (ι := ι) H (leOfHom h) d k ⟨m.val, m.property⟩
    have hn := projectiveModuleScalarGradedAwayLinearEquivOfEq_restriction
      (R := R) (P := MvPolynomial ι R) (Q := MvPolynomial ι B) (M := N)
      (projectiveLaurentDenominator_sdiff R (leOfHom h)).symm
      (projectivePolynomialCoefficientDenominator (R := R) (B := B) T)
      (projectivePolynomialCoefficientDenominator (R := R) (B := B) U)
      (projectivePolynomialCoefficientDenominator (R := R) (B := B) (U \ T))
      (projectiveLaurentDenominator_sdiff B (leOfHom h)).symm
      (fun k ↦ (H (d + k • (T.card : ℤ))).restrictScalars R)
      (fun k ↦ (H (d + k • (U.card : ℤ))).restrictScalars R)
      (projectiveGradedChart_mul_mem (R := R) (M := N) (ι := ι) (fun n ↦ (H n).restrictScalars R) (leOfHom h) d)
      hQmem z
    change (projectiveGradedPolynomialCoefficientChangeLinearEquiv
      (R := R) (ι := ι) H U d
      (projectiveGradedAwayRestriction (projectiveLaurentDenominator_sdiff R (leOfHom h)).symm
        (fun k ↦ (H (d + k • (T.card : ℤ))).restrictScalars R)
        (fun k ↦ (H (d + k • (U.card : ℤ))).restrictScalars R)
        (projectiveGradedChart_mul_mem (R := R) (M := N) (ι := ι) (fun n ↦ (H n).restrictScalars R) (leOfHom h) d) z)).val =
      (projectiveGradedAwayRestriction (projectiveLaurentDenominator_sdiff B (leOfHom h)).symm
        (fun k ↦ H (d + k • (T.card : ℤ))) (fun k ↦ H (d + k • (U.card : ℤ)))
        (projectiveGradedChart_mul_mem (R := B) (M := N) (ι := ι) H (leOfHom h) d)
        (projectiveGradedPolynomialCoefficientChangeLinearEquiv (R := R) (ι := ι) H T d z)).val
    dsimp only [projectiveGradedPolynomialCoefficientChangeLinearEquiv, LinearEquiv.trans_apply]
    rw [projectiveGradedAwayScalarRestrictionLinearEquiv_val,
      projectiveGradedAwayRestriction_val, projectiveGradedAwayScalarRestrictionLinearEquiv_val]
    exact congrArg Subtype.val hn)

/-- 多項式の係数変更による Čech コホモロジーと、B 上のコホモロジーの係数制限との同型。
原典 Stacks 30.20.1 の Hⁱ に対応する Čech 版の Rees 比較に使う。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveGradedPolynomialCoefficientChangeCechHomologyIso (d : ℤ) (q : ℕ) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).mapIso
    ((fullCechComplexFunctor (R := R) (ι := ι)).mapIso
      (projectiveGradedPolynomialCoefficientChangeChartIso (R := R) (B := B) (ι := ι) (N := N) H d)) ≪≫
    projectiveCechRestrictScalarsHomologyIso (algebraMap R B)
      (projectiveGradedModuleChartDiagram (R := B) (M := N) (ι := ι) H d) q

end SerrePositivity.AlgebraicGeometry
