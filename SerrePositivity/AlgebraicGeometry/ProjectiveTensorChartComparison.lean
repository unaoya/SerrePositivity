module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedTensorCoefficientChange
public import SerrePositivity.AlgebraicGeometry.ProjectiveTensorGradedChart
public import SerrePositivity.AlgebraicGeometry.ProjectivePolynomialCoefficientChange

/-!
概要：基底変更後の多項式加群の各標準開を、元の標準開のテンソル積と比較する。
方針：負次数の零延長とテンソル像の交換を示し、分数の B 線形比較を適用する。
規約：同型は各標準開の指定次数部分について述べ、平坦性を仮定する。
使われ方：Čech 底変換の比較先を、実際の基底変更後の標準開へつなぐ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped TensorProduct
universe u
variable {R B M : Type u} {ι : Type} [CommRing R] [CommRing B] [Algebra R B]
variable [DecidableEq ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
local instance projectiveTensorComparisonCoefficientModule {V : Type*}
    [AddCommGroup V] [Module R V] : Module B (V ⊗[R] B) := tensorRightCoefficientModule
local instance projectiveTensorComparisonCoefficientTower {V : Type*}
    [AddCommGroup V] [Module R V] : IsScalarTower R B (V ⊗[R] B) :=
  tensorRightCoefficient_scalarTower
local instance projectiveTensorComparisonPolynomialModule :
    Module (MvPolynomial ι B) (M ⊗[R] B) := projectiveTensorPolynomialModule
local instance projectiveTensorComparisonBPolynomialTower :
    IsScalarTower B (MvPolynomial ι B) (M ⊗[R] B) :=
  projectiveTensorPolynomial_coefficient_scalarTower
local instance projectiveTensorComparisonRPolynomialTower :
    IsScalarTower R (MvPolynomial ι B) (M ⊗[R] B) :=
  projectiveTensorPolynomial_base_scalarTower
local instance projectiveTensorComparisonPolynomialAlgebra :
    Algebra (MvPolynomial ι R) (MvPolynomial ι B) :=
  (MvPolynomial.map (algebraMap R B)).toAlgebra
local instance projectiveTensorComparisonPolynomialRingTower :
    IsScalarTower R (MvPolynomial ι R) (MvPolynomial ι B) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change MvPolynomial.C (algebraMap R B r) =
    MvPolynomial.map (algebraMap R B) (MvPolynomial.C r)
  rw [MvPolynomial.map_C]
local instance projectiveTensorComparisonPolynomialTower :
    IsScalarTower (MvPolynomial ι R) (MvPolynomial ι B) (M ⊗[R] B) :=
  projectiveTensorPolynomial_polynomial_scalarTower

variable (G : ℕ → Submodule R M)

/-- 負次数を零に延ばす操作は、次数成分のテンソル像と交換する。 -/
theorem projectiveTensorPiece_int (j : ℤ) :
    LinearMap.range (tensorRightCoefficientMap (B := B)
      (projectiveNatGradingInt G j).subtype) =
    projectiveNatGradingInt (projectiveTensorPiece (B := B) G) j := by
  by_cases hj : 0 ≤ j
  · rw [show projectiveNatGradingInt G j = G j.toNat from if_pos hj,
      show projectiveNatGradingInt (projectiveTensorPiece (B := B) G) j =
        projectiveTensorPiece (B := B) G j.toNat from if_pos hj]
    rfl
  · rw [show projectiveNatGradingInt G j = ⊥ from if_neg hj,
      show projectiveNatGradingInt (projectiveTensorPiece (B := B) G) j = ⊥ from if_neg hj]
    apply le_antisymm _ bot_le
    rintro x ⟨w, rfl⟩
    have hw : w = 0 := Subsingleton.elim _ _
    rw [hw, map_zero]
    exact Submodule.zero_mem _

variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
local instance projectiveTensorComparisonGradedAction :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B)
      (projectiveTensorPiece (B := B) G) := projectiveTensorPiece_gradedSMul (ι := ι) G
local instance projectiveTensorComparisonIntGradedAction :
    SetLike.GradedSMul
      (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt G) := projectiveNatGradingIntSMul (ι := ι) G

/-- 分母の冪ごとのテンソル像は、基底変更後の指定次数の分子と一致する。 -/
theorem projectiveTensorChartNumerator_eq (T : Finset ι) (d : ℤ) :
    projectiveTensorCoefficientNumerator (B := B)
      (fun n ↦ projectiveNatGradingInt G (d + n • (T.card : ℤ))) =
    (fun n ↦ projectiveNatGradingInt (projectiveTensorPiece (B := B) G)
      (d + n • (T.card : ℤ))) := by
  funext n
  exact projectiveTensorPiece_int G _

/-- 基底変更後の各標準開の指定次数部分と、元の標準開の右テンソル積との B 線形同型。 -/
def projectiveTensorChartRightLinearEquiv [Module.Flat R B] (T : Finset ι) (d : ℤ) :
    ((projectiveNatGradedModuleChartDiagram (ι := ι) G d).obj T) ⊗[R] B ≃ₗ[B]
      (projectiveTensorGradedModuleChartDiagram (B := B) (ι := ι) G d).obj T :=
  (projectiveGradedTensorCoefficientLinearEquiv
    (projectiveLaurentDenominator R T) (projectiveLaurentDenominator B T)
    (projectivePolynomialCoefficientDenominator (R := R) (B := B) T)
    (fun n ↦ projectiveNatGradingInt G (d + n • (T.card : ℤ)))
    (projectiveGradedChart_mul_denominator (projectiveNatGradingInt G) T d)).trans
      (LinearEquiv.ofEq _ _ (congrArg (projectiveGradedAway
        (projectiveLaurentDenominator B T)) (projectiveTensorChartNumerator_eq G T d)))

/-- 基底変更後の各標準開の指定次数部分と、元の標準開の左テンソル積との B 線形同型。 -/
def projectiveTensorChartLinearEquiv [Module.Flat R B] (T : Finset ι) (d : ℤ) :
    B ⊗[R] ((projectiveNatGradedModuleChartDiagram (ι := ι) G d).obj T) ≃ₗ[B]
      (projectiveTensorGradedModuleChartDiagram (B := B) (ι := ι) G d).obj T :=
  tensorRightCoefficientComm.symm.trans (projectiveTensorChartRightLinearEquiv G T d)

/-- 右テンソルによる標準開の比較は、指定次数の純テンソル分数を保つ。 -/
theorem projectiveTensorChartRightLinearEquiv_fraction [Module.Flat R B]
    (T : Finset ι) (d : ℤ) (n : ℕ)
    (m : projectiveNatGradingInt G (d + n • (T.card : ℤ))) (b : B)
    (u : (projectiveNatGradedModuleChartDiagram (ι := ι) G d).obj T)
    (hu : u.val = projectiveGradedFraction (projectiveLaurentDenominator R T)
      (fun k ↦ projectiveNatGradingInt G (d + k • (T.card : ℤ))) n m) :
    (projectiveTensorChartRightLinearEquiv (B := B) G T d (u ⊗ₜ[R] b)).val =
      LocalizedModule.mk (m.val ⊗ₜ[R] b)
        (projDenominator (projectiveLaurentDenominator B T) n) := by
  change (projectiveGradedTensorCoefficientEquiv
    (projectiveLaurentDenominator R T) (projectiveLaurentDenominator B T)
    (projectivePolynomialCoefficientDenominator (R := R) (B := B) T)
    (fun k ↦ projectiveNatGradingInt G (d + k • (T.card : ℤ))) (u ⊗ₜ[R] b)).val = _
  exact projectiveGradedTensorCoefficientEquiv_fraction
    (R := R) (B := B) (P := MvPolynomial ι R) (Q := MvPolynomial ι B) (M := M)
    (projectiveLaurentDenominator R T) (projectiveLaurentDenominator B T)
    (projectivePolynomialCoefficientDenominator (R := R) (B := B) T)
    (fun k ↦ projectiveNatGradingInt G (d + k • (T.card : ℤ))) n m b u hu

/-- 左テンソルによる標準開の比較も、指定次数の純テンソル分数を保つ。 -/
theorem projectiveTensorChartLinearEquiv_fraction [Module.Flat R B]
    (T : Finset ι) (d : ℤ) (n : ℕ)
    (m : projectiveNatGradingInt G (d + n • (T.card : ℤ))) (b : B)
    (u : (projectiveNatGradedModuleChartDiagram (ι := ι) G d).obj T)
    (hu : u.val = projectiveGradedFraction (projectiveLaurentDenominator R T)
      (fun k ↦ projectiveNatGradingInt G (d + k • (T.card : ℤ))) n m) :
    (projectiveTensorChartLinearEquiv (B := B) G T d (b ⊗ₜ[R] u)).val =
      LocalizedModule.mk (m.val ⊗ₜ[R] b)
        (projDenominator (projectiveLaurentDenominator B T) n) := by
  change (projectiveTensorChartRightLinearEquiv (B := B) G T d
    ((TensorProduct.comm R B _) (b ⊗ₜ[R] u))).val = _
  rw [TensorProduct.comm_tmul]
  exact projectiveTensorChartRightLinearEquiv_fraction G T d n m b u hu

end SerrePositivity.AlgebraicGeometry
