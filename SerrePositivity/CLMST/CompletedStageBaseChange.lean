module

public import SerrePositivity.CLMST.StageTensor
public import SerrePositivity.CommutativeAlgebra.RootTower.CompletionFlat
public import SerrePositivity.HomologicalAlgebra.FlatBaseChange
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # 完備塔への基底変更と有限段

`C=A∞`、`B=A_n`、`D_n=B⊗_A D` として、`C⊗_B D_n` と `C⊗_A D` を
C 代数として同定する。D_n の標準像が既存の段写像と一致することを確認し、
Noether 基底上の完備塔の平坦性を D_n 上の平坦性へ移す。
右因子の代数構造は局所的に指定し、大域的なインスタンスは追加しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open scoped TensorProduct
namespace SerrePositivity.CLMST
open Section2

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- テンソル環の構成では、有限段の完備塔上の作用を代数から得られる加群構造で固定する。
このインスタンスの登録は本ファイル内だけに限る。 -/
local instance completedStageModule (n : ℕ) :
    Module (TowerStage A t p n) (CompletedTower A t p) := Algebra.toModule

/-- 有限段で先に基底変更してから完備塔へ移す操作は、基底環からの直接の基底変更と同型。 -/
def completedStageBaseChangeEquiv (n : ℕ) :
    (CompletedTower A t p) ⊗[TowerStage A t p n] (StageAlgebra A D t p n) ≃ₐ[CompletedTower A t p]
      (CompletedTower A t p) ⊗[A] D :=
  Algebra.TensorProduct.cancelBaseChange A (TowerStage A t p n)
    (CompletedTower A t p) (CompletedTower A t p) D

/-- 同型は、三つの因子からなる単純テンソルを標準の積へ送る。 -/
@[simp] theorem completedStageBaseChangeEquiv_tmul (n : ℕ)
    (c : CompletedTower A t p) (b : TowerStage A t p n) (d : D) :
    completedStageBaseChangeEquiv A D t p n (c ⊗ₜ[TowerStage A t p n] (b ⊗ₜ[A] d)) =
      (algebraMap (TowerStage A t p n) (CompletedTower A t p) b * c) ⊗ₜ[A] d := by
  exact Algebra.TensorProduct.cancelBaseChange_tmul _ _ _ _ _ _ _ _

/-- 有限段の右因子を含めてから基底変更同型を適用すると、既存の標準段写像となる。 -/
theorem completedStageBaseChangeEquiv_includeRight_apply (n : ℕ)
    (x : StageAlgebra A D t p n) :
    completedStageBaseChangeEquiv A D t p n
      ((Algebra.TensorProduct.includeRight : StageAlgebra A D t p n →ₐ[TowerStage A t p n]
        (CompletedTower A t p) ⊗[TowerStage A t p n] (StageAlgebra A D t p n)) x) =
      stageToCompletedTensor A D t p n x := by
  change TowerStage A t p n ⊗[A] D at x
  induction x using TensorProduct.inductionOn with
  | tmul b d =>
    change completedStageBaseChangeEquiv A D t p n
      ((1 : CompletedTower A t p) ⊗ₜ[TowerStage A t p n] (b ⊗ₜ[A] d)) = _
    rw [completedStageBaseChangeEquiv_tmul, mul_one, stageToCompletedTensor_tmul]
    rfl
  | add x y hx hy =>
    simp only [map_add, hx, hy]

/-- 右因子の標準写像との両立を環準同型の等式として公開する。 -/
theorem completedStageBaseChangeEquiv_comp_includeRight (n : ℕ) :
    (completedStageBaseChangeEquiv A D t p n).toRingHom.comp
      (Algebra.TensorProduct.includeRight : StageAlgebra A D t p n →ₐ[TowerStage A t p n]
        (CompletedTower A t p) ⊗[TowerStage A t p n] (StageAlgebra A D t p n)).toRingHom =
      (stageToCompletedTensor A D t p n).toRingHom := by
  ext x
  exact completedStageBaseChangeEquiv_includeRight_apply A D t p n x

/-- 完備テンソル代数への有限段の作用は、既存の標準段写像から定める。
利用先で局所インスタンスとして置くための名前付き代数構造。 -/
@[instance_reducible] def completedTensorStageAlgebra (n : ℕ) :
    Algebra (StageAlgebra A D t p n) ((CompletedTower A t p) ⊗[A] D) :=
  (stageToCompletedTensor A D t p n).toRingHom.toAlgebra

attribute [local instance] completedTensorStageAlgebra

/-- 段の左作用も、テンソル代数の標準の代数構造から得られる加群構造で固定する。 -/
local instance completedTensorBaseStageModule (n : ℕ) :
    Module (TowerStage A t p n) ((CompletedTower A t p) ⊗[A] D) := Algebra.toModule

/-- 段のスカラー作用を、同じ標準の代数構造の作用で局所的に固定する。 -/
local instance completedTensorBaseStageSMul (n : ℕ) :
    SMul (TowerStage A t p n) ((CompletedTower A t p) ⊗[A] D) :=
  (inferInstance : Algebra (TowerStage A t p n) ((CompletedTower A t p) ⊗[A] D)).toSMul

/-- 有限段 B から D_n を経由する作用は、完備塔 C を経由する標準作用と両立する。 -/
theorem completedTensorStageScalarTower (n : ℕ) :
    IsScalarTower (TowerStage A t p n) (StageAlgebra A D t p n)
      ((CompletedTower A t p) ⊗[A] D) := by
  apply IsScalarTower.of_algebraMap_eq
  intro b
  change algebraMap (TowerStage A t p n) ((CompletedTower A t p) ⊗[A] D) b =
    stageToCompletedTensor A D t p n
      (algebraMap (TowerStage A t p n) (StageAlgebra A D t p n) b)
  change algebraMap (TowerStage A t p n) (CompletedTower A t p) b ⊗ₜ[A] 1 =
    stageToCompletedTensor A D t p n (b ⊗ₜ[A] 1)
  rw [stageToCompletedTensor_tmul]
  rfl

/-- 完備テンソル代数は、有限段 B の完備塔 C と D_n による標準押し出し。
右因子の作用を、実際の段写像に固定した形で供給する。 -/
theorem completedTensorStageIsPushout (n : ℕ) :
    letI := completedTensorStageScalarTower A D t p n
    Algebra.IsPushout (TowerStage A t p n) (CompletedTower A t p)
      (StageAlgebra A D t p n) ((CompletedTower A t p) ⊗[A] D) := by
  let := completedTensorStageScalarTower A D t p n
  constructor
  apply IsBaseChange.of_equiv (completedStageBaseChangeEquiv A D t p n).toLinearEquiv
  intro x
  exact completedStageBaseChangeEquiv_includeRight_apply A D t p n x

/-- Noether 基底上では、完備テンソル代数は任意の基底変更した有限段 D_n 上で平坦。
D の有限性は不要であり、完備塔の B 上の平坦性を押し出しで移す。 -/
theorem flat_completedTensor_over_stage [IsNoetherianRing A] [Fact p.Prime] (n : ℕ) :
    Module.Flat (StageAlgebra A D t p n) ((CompletedTower A t p) ⊗[A] D) := by
  let := completedTensorStageScalarTower A D t p n
  let := completedTensorStageIsPushout A D t p n
  let := flat_completedTower_over_stage A t p n
  exact flat_of_algebra_isPushout (TowerStage A t p n) (CompletedTower A t p)
    (StageAlgebra A D t p n) ((CompletedTower A t p) ⊗[A] D)

end SerrePositivity.CLMST
