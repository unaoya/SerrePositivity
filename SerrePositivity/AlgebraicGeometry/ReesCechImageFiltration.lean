module

public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveCechTransition

/-!
概要：各 IⁿM の Čech コホモロジーの像を、元のコホモロジーの I フィルトレーションにする。
方針：遷移と係数の持ち上げ・次数移動の可換式で像の包含を示す。
規約：ここでは Noether 性や有限生成性を仮定しない。
使われ方：Stacks 30.20.4(1) の Hⁱ の核の評価に渡す、実際の Čech 像のフィルトレーション。
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

local instance reesCechImagePolynomialModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
local instance reesCechImageTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance reesCechImageGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectivePiece (ι := ι) I G n) :=
  reesAdicProjectivePieceGradedSMul (ι := ι) I G n

/-- IⁿM の、固定した Proj・Čech 次数のコホモロジーの対象。 -/
abbrev reesAdicProjectiveCechStage (n : ℕ) (d : ℤ) (q : ℕ) : ModuleCat.{u} R :=
  (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι)
    (reesAdicProjectivePiece (ι := ι) I G n) d)).homology q

/-- 各 IⁿM の Čech コホモロジーからの包含の像。
原典 Stacks 30.20.4(1) の Hⁱ の像に対応する Čech 版の部分加群。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesAdicProjectiveCechImage (n : ℕ) (d : ℤ) (q : ℕ) :
    Submodule R (reesAdicProjectiveCechTarget (R := R) (M := M) (ι := ι) G d q) :=
  LinearMap.range (reesAdicProjectiveCechToModule (R := R) (M := M) (ι := ι) I G n d q).hom

/-- Čech コホモロジーの像は、I 進指数について減少する。
原典 Stacks 30.20.4(1) の Hⁱ の像に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveCechImage_antitone (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveCechImage (R := R) (M := M) (ι := ι) I G i d q ≤
      reesAdicProjectiveCechImage (R := R) (M := M) (ι := ι) I G j d q := by
  intro y hy
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
  refine LinearMap.mem_range.mpr ⟨
    (reesAdicProjectiveCechTransition (R := R) (M := M) (ι := ι) I G i j h d q).hom x, ?_⟩
  have hcat := reesAdicProjectiveCechToModule_transition
    (R := R) (M := M) (ι := ι) I G i j h d q
  have hx := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hcat) x
  exact hx

/-- Iⁱ と第 j 段の Čech 像の積は、第 i+j 段の像に入る。
原典 Stacks 30.20.4(1) の Hⁱ の像の Rees 作用に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveCechImage_pow_smul_le (i j : ℕ) (d : ℤ) (q : ℕ) :
    I ^ i • reesAdicProjectiveCechImage (R := R) (M := M) (ι := ι) I G j d q ≤
      reesAdicProjectiveCechImage (R := R) (M := M) (ι := ι) I G (i + j) d q := by
  apply Submodule.smul_le.mpr
  intro a ha y hy
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
  refine LinearMap.mem_range.mpr ⟨
    (reesAdicProjectiveDegreeShiftCechHomologyMap (R := R) (M := M) (ι := ι) I G i j a ha d q).hom x, ?_⟩
  have hcat := reesAdicProjectiveCechToModule_degreeShift
    (R := R) (M := M) (ι := ι) I G i j a ha d q
  have hx := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hcat) x
  change (reesAdicProjectiveCechToModule (R := R) (M := M) (ι := ι) I G (i + j) d q).hom
      ((reesAdicProjectiveDegreeShiftCechHomologyMap
        (R := R) (M := M) (ι := ι) I G i j a ha d q).hom x) =
    a • (reesAdicProjectiveCechToModule (R := R) (M := M) (ι := ι) I G j d q).hom x at hx
  exact hx

/-- 通常の Iⁿ 倍は、第 n 段からの Čech 像に入る。
原典 Stacks 30.20.4(1) の Hⁱ の I 進評価に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveCechImage_contains_pow (n : ℕ) (d : ℤ) (q : ℕ) :
    I ^ n • (⊤ : Submodule R (reesAdicProjectiveCechTarget
      (R := R) (M := M) (ι := ι) G d q)) ≤
      reesAdicProjectiveCechImage (R := R) (M := M) (ι := ι) I G n d q := by
  apply Submodule.smul_le.mpr
  intro a ha x _hx
  refine LinearMap.mem_range.mpr ⟨
    (reesAdicProjectiveCechCoefficientLift (R := R) (M := M) (ι := ι) I G n a ha d q).hom x, ?_⟩
  have hcat := reesAdicProjectiveCechToModule_coefficientLift
    (R := R) (M := M) (ι := ι) I G n a ha d q
  have hx := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hcat) x
  change (reesAdicProjectiveCechToModule (R := R) (M := M) (ι := ι) I G n d q).hom
    ((reesAdicProjectiveCechCoefficientLift
      (R := R) (M := M) (ι := ι) I G n a ha d q).hom x) = a • x at hx
  exact hx

/-- 各 IⁿM の Čech 像からなる、元のコホモロジーの実際の I フィルトレーション。
原典 Stacks 30.20.4(1) の Hⁱ の核の評価に渡す Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def reesAdicProjectiveCechImageFiltration (d : ℤ) (q : ℕ) :
    I.Filtration (reesAdicProjectiveCechTarget (R := R) (M := M) (ι := ι) G d q) where
  N n := reesAdicProjectiveCechImage (R := R) (M := M) (ι := ι) I G n d q
  mono n := reesAdicProjectiveCechImage_antitone (R := R) (M := M) (ι := ι) I G (n + 1) n
    (Nat.le_succ n) d q
  smul_le n := by
    simpa only [pow_one, Nat.one_add] using
      reesAdicProjectiveCechImage_pow_smul_le (R := R) (M := M) (ι := ι) I G 1 n d q

/-- 各段の Čech コホモロジーを、その像へ制限した線形写像。 -/
def reesAdicProjectiveCechImageStageMap (n : ℕ) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveCechStage (R := R) (M := M) (ι := ι) I G n d q →ₗ[R]
      reesAdicProjectiveCechImage (R := R) (M := M) (ι := ι) I G n d q :=
  (reesAdicProjectiveCechToModule (R := R) (M := M) (ι := ι) I G n d q).hom.rangeRestrict

/-- 像へ制限した各段の Čech 写像は全射。 -/
theorem reesAdicProjectiveCechImageStageMap_surjective (n : ℕ) (d : ℤ) (q : ℕ) :
    Function.Surjective (reesAdicProjectiveCechImageStageMap
      (R := R) (M := M) (ι := ι) I G n d q) := by
  intro y
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp y.property
  exact ⟨x, Subtype.ext hx⟩

end SerrePositivity.AlgebraicGeometry
