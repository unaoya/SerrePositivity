module

public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGrading
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor

/-!
概要：自然数次数を保つ加群写像を、標準開の図式と Čech コホモロジーの写像にする。
方針：負の次数を零に延ばして、整数次数の斉次局所化の写像を使う。
規約：加群写像は多項式環上線形で、Proj 次数を保つ。
使われ方：Rees 単項式の作用を、各 IⁿM の Čech コホモロジーへ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory

universe u
variable {R M N : Type u} {ι : Type} [CommRing R] [DecidableEq ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable (G : ℕ → Submodule R M) (H : ℕ → Submodule R N)
variable (f : M →ₗ[MvPolynomial ι R] N)
variable (hf : ∀ n, ∀ m ∈ G n, f m ∈ H n)
include hf

/-- 自然数次数を保つ写像は、負の成分を零に延ばした次数も保つ。 -/
theorem projectiveNatGradingInt_map_mem (d : ℤ) (m : M)
    (hm : m ∈ projectiveNatGradingInt G d) :
    f m ∈ projectiveNatGradingInt H d := by
  by_cases hd : 0 ≤ d
  · simp only [projectiveNatGradingInt, hd, ite_true] at hm ⊢
    exact hf d.toNat m hm
  · simp only [projectiveNatGradingInt, hd, ite_false, Submodule.mem_bot] at hm ⊢
    rw [hm, map_zero]

variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]

/-- 自然数の Proj 次数を保つ写像が誘導する、標準開の係数図式の写像。 -/
def projectiveNatGradedModuleChartMap (d : ℤ) :=
  letI := projectiveNatGradingIntSMul (ι := ι) G
  letI := projectiveNatGradingIntSMul (ι := ι) H
  projectiveGradedModuleChartMap (R := R) (ι := ι)
    (projectiveNatGradingInt G) (projectiveNatGradingInt H) d f
    (projectiveNatGradingInt_map_mem G H f hf)

/-- 次数を保つ写像が誘導する、標準開 Čech コホモロジーの写像。
原典 Stacks 30.20.1 の Hⁱ の次数ごとの作用に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveNatGradedModuleCechHomologyMap (d : ℤ) (q : ℕ) :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) q).map
    (fullCechComplexMap (projectiveNatGradedModuleChartMap G H f hf d))

end SerrePositivity.AlgebraicGeometry
