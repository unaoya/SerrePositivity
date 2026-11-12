module

public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveTransition
public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveCechDegreeShift
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGradedChartMapLaws

/-!
概要：I 進各段から元の加群への写像と遷移を Čech コホモロジーへ移す。
方針：次数を保つ線形写像と、Čech 写像の合成則を使う。
規約：基底環・Proj 次数・Čech 次数を固定し、I 進指数を動かす。
使われ方：原典 Stacks 30.20.4 の Hⁱ の核・像に対応する Čech 版のフィルトレーション。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory

universe u
variable {R M : Type u} {ι : Type} [CommRing R] [DecidableEq ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance reesCechTransitionPolynomialModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
local instance reesCechTransitionTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance reesCechTransitionGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectivePiece (ι := ι) I G n) :=
  reesAdicProjectivePieceGradedSMul (ι := ι) I G n

/-- 元の加群の、固定した Proj・Čech 次数のコホモロジーの対象。 -/
abbrev reesAdicProjectiveCechTarget (d : ℤ) (q : ℕ) : ModuleCat.{u} R :=
  (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G d)).homology q

/-- 各 IⁿM の Čech コホモロジーから、元の加群の同じコホモロジーへの写像。
原典 Stacks 30.20.4 の Hⁱ の像に対応する Čech 版の写像。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesAdicProjectiveCechToModule (n : ℕ) (d : ℤ) (q : ℕ) :=
  projectiveNatGradedModuleCechHomologyMap (R := R) (ι := ι)
    (reesAdicProjectivePiece (ι := ι) I G n) G
    (reesAdicProjectiveToModule (ι := ι) (M := M) I n)
    (fun k m hm ↦ reesAdicProjectiveToModule_preservesPiece I G n k m hm) d q

/-- IⁱM→IʲM の遷移が誘導する Čech コホモロジーの写像。
原典 Stacks 30.20.4 の Hⁱ の逆系に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesAdicProjectiveCechTransition (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ) :=
  projectiveNatGradedModuleCechHomologyMap (R := R) (ι := ι)
    (reesAdicProjectivePiece (ι := ι) I G i) (reesAdicProjectivePiece (ι := ι) I G j)
    (reesAdicProjectiveTransition (ι := ι) (M := M) I i j h)
    (fun k m hm ↦ reesAdicProjectiveTransition_preservesPiece I G i j k h m hm) d q

/-- Iⁿ の係数の持ち上げが誘導する、Čech コホモロジーの写像。
原典 Stacks 30.20.4(1) の Hⁱ の I 進核の評価に対応する Čech 版の入力。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesAdicProjectiveCechCoefficientLift (n : ℕ) (a : R) (ha : a ∈ I ^ n) (d : ℤ) (q : ℕ) :=
  projectiveNatGradedModuleCechHomologyMap (R := R) (ι := ι)
    G (reesAdicProjectivePiece (ι := ι) I G n)
    (reesAdicProjectiveCoefficientLift (ι := ι) (M := M) I n a ha)
    (fun k m hm ↦ reesAdicProjectiveCoefficientLift_preservesPiece I G n k a ha m hm) d q

/-- Čech 遷移と元のコホモロジーへの包含は可換。
原典 Stacks 30.20.4 の Hⁱ の逆系に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveCechToModule_transition
    (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveCechTransition (R := R) (M := M) (ι := ι) I G i j h d q ≫
      reesAdicProjectiveCechToModule (R := R) (M := M) (ι := ι) I G j d q =
    reesAdicProjectiveCechToModule (R := R) (M := M) (ι := ι) I G i d q := by
  simp only [reesAdicProjectiveCechTransition, reesAdicProjectiveCechToModule]
  rw [projectiveNatGradedModuleCechHomologyMap_comp]
  congr 1

/-- Čech 遷移の合成は、指数の合成に一致。
原典 Stacks 30.20.4 の Hⁱ の逆系に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveCechTransition_comp
    (i j k : ℕ) (hij : j ≤ i) (hjk : k ≤ j) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveCechTransition (R := R) (M := M) (ι := ι) I G i j hij d q ≫
      reesAdicProjectiveCechTransition (R := R) (M := M) (ι := ι) I G j k hjk d q =
    reesAdicProjectiveCechTransition (R := R) (M := M) (ι := ι) I G i k (hjk.trans hij) d q := by
  simp only [reesAdicProjectiveCechTransition]
  rw [projectiveNatGradedModuleCechHomologyMap_comp]
  congr 1

/-- Čech の次数移動を元のコホモロジーへ送ると、基底係数の作用になる。
原典 Stacks 30.20.1 の Hⁱ の Rees 作用に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveCechToModule_degreeShift
    (i j : ℕ) (a : R) (ha : a ∈ I ^ i) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveDegreeShiftCechHomologyMap (R := R) (M := M) (ι := ι) I G i j a ha d q ≫
      reesAdicProjectiveCechToModule (R := R) (M := M) (ι := ι) I G (i + j) d q =
    reesAdicProjectiveCechToModule (R := R) (M := M) (ι := ι) I G j d q ≫
      (a • 𝟙 (reesAdicProjectiveCechTarget (R := R) (M := M) (ι := ι) G d q)) := by
  rw [← projectiveNatGradedModuleCechHomologyMap_baseScalar (ι := ι) G a d q]
  simp only [reesAdicProjectiveDegreeShiftCechHomologyMap, reesAdicProjectiveCechToModule]
  rw [projectiveNatGradedModuleCechHomologyMap_comp, projectiveNatGradedModuleCechHomologyMap_comp]
  congr 1

/-- 係数の持ち上げと包含は、元の Čech コホモロジーのスカラー作用を与える。
原典 Stacks 30.20.4(1) の Hⁱ の I 進評価に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveCechToModule_coefficientLift
    (n : ℕ) (a : R) (ha : a ∈ I ^ n) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveCechCoefficientLift (R := R) (M := M) (ι := ι) I G n a ha d q ≫
      reesAdicProjectiveCechToModule (R := R) (M := M) (ι := ι) I G n d q =
    a • 𝟙 (reesAdicProjectiveCechTarget (R := R) (M := M) (ι := ι) G d q) := by
  rw [← projectiveNatGradedModuleCechHomologyMap_baseScalar (ι := ι) G a d q]
  simp only [reesAdicProjectiveCechCoefficientLift, reesAdicProjectiveCechToModule]
  rw [projectiveNatGradedModuleCechHomologyMap_comp]
  congr 1

/-- 十分 I 進的な係数による Čech 次数移動の遷移は、元のコホモロジーを経由。
原典 Stacks 30.20.4(3) の Hⁱ の核の遷移の零化に対応する Čech 版の因子分解。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveCechTransition_degreeShift_factor
    (i j n : ℕ) (hn : n ≤ i) (a : R) (ha : a ∈ I ^ i) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveDegreeShiftCechHomologyMap (R := R) (M := M) (ι := ι) I G i j a ha d q ≫
      reesAdicProjectiveCechTransition (R := R) (M := M) (ι := ι) I G (i + j) n
        (hn.trans (Nat.le_add_right i j)) d q =
    reesAdicProjectiveCechToModule (R := R) (M := M) (ι := ι) I G j d q ≫
      reesAdicProjectiveCechCoefficientLift (R := R) (M := M) (ι := ι) I G n a
        ((Ideal.pow_le_pow_right hn) ha) d q := by
  simp only [reesAdicProjectiveDegreeShiftCechHomologyMap,
    reesAdicProjectiveCechTransition, reesAdicProjectiveCechToModule,
    reesAdicProjectiveCechCoefficientLift]
  rw [projectiveNatGradedModuleCechHomologyMap_comp, projectiveNatGradedModuleCechHomologyMap_comp]
  congr 1

end SerrePositivity.AlgebraicGeometry
