module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedChartDirectSum
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGrading

/-!
概要：自然数次数の直和の比較を、標準開と Čech コホモロジーへ移す。
方針：負の次数を零に延ばし、整数次数の図式の直和比較を適用する。
規約：分子の次数の対応から、全体の加群の次数付き作用も移せる。
使われ方：原典 Stacks 30.20.1 の Hⁱ に対応する Čech 版の Rees 次数の直和比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped DirectSum

universe u
variable {R : Type u} [CommRing R] {ι κ : Type} [DecidableEq ι] [Fintype ι] [DecidableEq κ]
variable {F : κ → Type u} [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
variable [∀ i, Module (MvPolynomial ι R) (F i)]
variable [∀ i, IsScalarTower R (MvPolynomial ι R) (F i)]
variable {N : Type u} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable (G : ∀ i, ℕ → Submodule R (F i)) (H : ℕ → Submodule R N)
variable (e : (⨁ i, F i) ≃ₗ[MvPolynomial ι R] N)
variable (he : ∀ d x, e x ∈ H d ↔ x ∈ projectiveDirectSumSubmodule (fun i ↦ G i d))

include he

/-- 自然数次数の直和の分子の対応は、負の次数を零に延ばしても成り立つ。 -/
theorem projectiveNatGradingInt_directSum_mem_iff (d : ℤ) (x : ⨁ i, F i) :
    e x ∈ projectiveNatGradingInt H d ↔
      x ∈ projectiveDirectSumSubmodule (fun i ↦ projectiveNatGradingInt (G i) d) := by
  by_cases hd : 0 ≤ d
  · simpa only [projectiveNatGradingInt, hd, ite_true] using he d.toNat x
  · simp only [mem_projectiveDirectSumSubmodule, projectiveNatGradingInt, hd, ite_false,
      Submodule.mem_bot]
    constructor
    · intro h
      have hx : x = 0 := e.injective (h.trans e.map_zero.symm)
      intro i
      rw [hx]
      rfl
    · intro hx
      have hz : x = 0 := DFinsupp.ext hx
      rw [hz, map_zero]

variable [∀ i, SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) (G i)]

/-- 各成分の次数付き作用を、次数を対応させる直和の同値で全体へ移す。 -/
theorem projectiveNatGradedSMul_of_directSumLinearEquiv :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H := by
  refine ⟨?_⟩
  intro i j a m ha hm
  change a • m ∈ H (i + j)
  have hx : e.symm m ∈ projectiveDirectSumSubmodule (fun n ↦ G n j) :=
    (he j (e.symm m)).mp (by simpa only [e.apply_symm_apply] using hm)
  have hx' : a • e.symm m ∈ projectiveDirectSumSubmodule (fun n ↦ G n (i + j)) := by
    rw [mem_projectiveDirectSumSubmodule] at hx ⊢
    intro n
    exact SetLike.GradedSMul.smul_mem
      (A := MvPolynomial.homogeneousSubmodule ι R) (B := G n) ha (hx n)
  have hy := (he (i + j) (a • e.symm m)).mpr hx'
  simpa only [map_smul, e.apply_symm_apply] using hy

variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]

/-- 自然数次数の直和の同値が誘導する標準開の係数図式の同型。 -/
def projectiveNatGradedModuleChartDirectSumIso (d : ℤ) :=
  letI : ∀ i, SetLike.GradedSMul
      (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt (G i)) := fun i ↦ projectiveNatGradingIntSMul (ι := ι) (G i)
  letI := projectiveNatGradingIntSMul (ι := ι) H
  projectiveGradedModuleChartDirectSumIso (R := R) (ι := ι) (κ := κ) (F := F) (N := N)
    (fun i ↦ projectiveNatGradingInt (G i)) (projectiveNatGradingInt H) e
    (projectiveNatGradingInt_directSum_mem_iff G H e he) d

/-- 自然数次数の直和の同値が誘導する、Čech 版のコホモロジーの直和同型。
原典 Stacks 30.20.1 の Hⁱ の直和に対応する Čech 版の比較。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveNatGradedModuleChartDirectSumCechHomologyIso (d : ℤ) (q : ℕ) :=
  letI : ∀ i, SetLike.GradedSMul
      (AddMonoidAlgebra.gradeBy R (projectivePolynomialDegree (ι := ι)))
      (projectiveNatGradingInt (G i)) := fun i ↦ projectiveNatGradingIntSMul (ι := ι) (G i)
  letI := projectiveNatGradingIntSMul (ι := ι) H
  projectiveGradedModuleChartDirectSumCechHomologyIso (R := R) (ι := ι) (κ := κ) (F := F) (N := N)
    (fun i ↦ projectiveNatGradingInt (G i)) (projectiveNatGradingInt H) e
    (projectiveNatGradingInt_directSum_mem_iff G H e he) d q

end SerrePositivity.AlgebraicGeometry
