module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFrobenius
public import SerrePositivity.AlgebraicGeometry.FrobeniusAdicQuotient

/-!
概要：実際の標準開から作った Čech Frobenius を I 進剰余系と完備化へ送る。
方針：半線形性による Iⁿ から I^(p*n) の制御を、商写像の代表元で計算する。
規約：ここでの商は Čech H 自身の I 進商であり、閉厚化の Čech H ではない。
使われ方：形式関数の同型と実際の閉厚化の Frobenius を照合する側の入口。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [DecidableEq ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R) (p : ℕ) (hp : p.Prime) [ExpChar R p] (hz : (p : A) = 0)
variable (G : ℕ → Submodule R A) [SetLike.GradedMonoid G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (d : ℤ) (q : ℕ)

/-- 実際の Čech Frobenius は、H の Iⁿ 倍を I^(p*n) 倍へ送る。
原典 BST13 Lemma 3.9(1) の Hⁱ の冪による評価に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveNatGradedCechFrobenius_ideal_power_control (n : ℕ) :
    I ^ n • (⊤ : Submodule R
      ((fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G d)).homology q)) ≤
    (I ^ (p * n) • (⊤ : Submodule R
      ((fullCechComplex
        (projectiveNatGradedModuleChartDiagram (ι := ι) G ((p : ℤ) * d))).homology q))).comap
      (projectiveNatGradedCechFrobenius (ι := ι) p hp hz G d q) :=
  frobeniusSemilinear_ideal_power_control I p
    (projectiveNatGradedCechFrobenius (ι := ι) p hp hz G d q) n

/-- Čech H 自身の I 進商上の Frobenius。指数 n を p*n へ送る。 -/
def projectiveNatGradedCechFrobeniusAdicQuotientMap (n : ℕ) :
    ((fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G d)).homology q) ⧸
        (I ^ n • (⊤ : Submodule R ((fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G d)).homology q))) →ₛₗ[frobenius R p]
      ((fullCechComplex
        (projectiveNatGradedModuleChartDiagram (ι := ι) G ((p : ℤ) * d))).homology q) ⧸
        (I ^ (p * n) • (⊤ : Submodule R ((fullCechComplex
        (projectiveNatGradedModuleChartDiagram (ι := ι) G ((p : ℤ) * d))).homology q))) :=
  frobeniusSemilinearShiftedQuotientMap I p
    (projectiveNatGradedCechFrobenius (ι := ι) p hp hz G d q) n

/-- I 進商の Frobenius は、元の Čech H の代表を実際の Frobenius で送る。 -/
@[simp] theorem projectiveNatGradedCechFrobeniusAdicQuotientMap_mk (n : ℕ)
    (x : ((fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G d)).homology q)) :
    projectiveNatGradedCechFrobeniusAdicQuotientMap (ι := ι) I p hp hz G d q n
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (projectiveNatGradedCechFrobenius (ι := ι) p hp hz G d q x) := rfl

/-- 指数 n→p*n の Čech Frobenius は、I 進商の遷移と可換。 -/
theorem projectiveNatGradedCechFrobeniusAdicQuotientMap_transition
    (i j : ℕ) (h : j ≤ i) :
    (AdicCompletion.transitionMap I _ (Nat.mul_le_mul_left p h)).comp
        (projectiveNatGradedCechFrobeniusAdicQuotientMap (ι := ι) I p hp hz G d q i) =
      (projectiveNatGradedCechFrobeniusAdicQuotientMap (ι := ι) I p hp hz G d q j).comp
        (AdicCompletion.transitionMap I _ h) :=
  frobeniusSemilinearShiftedQuotientMap_transition I p
    (projectiveNatGradedCechFrobenius (ι := ι) p hp hz G d q) i j h

/-- 実際の Čech Frobenius が誘導する、I 進完備化上の半線形写像。
原典 Stacks 30.20.4 と BS17 Lemma 4.6(i) の Hⁱ に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveNatGradedCechFrobeniusAdicCompletionMap :
    AdicCompletion I
        ((fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G d)).homology q)
      →ₛₗ[frobenius R p]
    AdicCompletion I
      ((fullCechComplex
        (projectiveNatGradedModuleChartDiagram (ι := ι) G ((p : ℤ) * d))).homology q) :=
  frobeniusSemilinearCompletionMap I p (projectiveNatGradedCechFrobenius (ι := ι) p hp hz G d q)

/-- 完備化上の Čech Frobenius は、元の H からの写像を保つ。 -/
theorem projectiveNatGradedCechFrobeniusAdicCompletionMap_of
    (x : ((fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι) G d)).homology q)) :
    projectiveNatGradedCechFrobeniusAdicCompletionMap (ι := ι) I p hp hz G d q
        (AdicCompletion.of I _ x) =
      AdicCompletion.of I _ (projectiveNatGradedCechFrobenius (ι := ι) p hp hz G d q x) :=
  frobeniusSemilinearCompletionMap_of I p
    (projectiveNatGradedCechFrobenius (ι := ι) p hp hz G d q) x

end SerrePositivity.AlgebraicGeometry
