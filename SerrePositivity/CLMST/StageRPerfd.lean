module

public import SerrePositivity.CLMST.Algebra
public import SerrePositivity.CommutativeAlgebra.RootTower.BaseChange

/-! # 有限段から `RPerfd` への写像

## 概要

根の塔の有限段の基底変更 `Section2.StageAlgebra`（CommutativeAlgebra/RootTower/BaseChange）から `RPerfd = (A∞ ⊗[A] D)_perfd` への標準の `D` 代数写像 `toRPerfd` を作り、`D` の作用との両立と、完備テンソル積を経由する `toMixedPerfectoid` との一致を示す。

## 規約

旧 `CLMST/Section2.StageAlgebra`・`StageTensor` の `RPerfd` を使う部分（基礎の部分は 2a で CommutativeAlgebra/RootTower/BaseChange へ下ろした）。

## 使われ方

CLMST の Cor 4.0.4・Prop 4.0.14 の有限段の評価。
-/

@[expose] public noncomputable section

universe u

open scoped TensorProduct
open IsLocalRing

namespace SerrePositivity.CLMST
open Section2

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ)

variable [IsNoetherianRing A] [Module.Finite A D] [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

/-- 有限段から塔・完備化を経由して `RPerfd` へ送る A 代数写像。 -/
def stageToRPerfd (n : ℕ) : TowerStage A t p n →ₐ[A] RPerfd A D t p hperf :=
  (IsScalarTower.toAlgHom A (CompletedTower A t p) (RPerfd A D t p hperf)).comp
    ((IsScalarTower.toAlgHom A (Tower A t p) (CompletedTower A t p)).comp
      (IsScalarTower.toAlgHom A (TowerStage A t p n) (Tower A t p)))

/-- 有限段の基底変更から `RPerfd` への標準 D 代数写像。 -/
def toRPerfd (n : ℕ) : Section2.StageAlgebra A D t p n →ₐ[D] RPerfd A D t p hperf := by
  letI : Algebra D (TowerStage A t p n ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
  exact (Algebra.TensorProduct.lift (Algebra.ofId D (RPerfd A D t p hperf))
    (stageToRPerfd A D t p hperf n) (fun _ _ ↦ Commute.all _ _)).comp
      (Algebra.TensorProduct.commRight A D (TowerStage A t p n)).symm.toAlgHom

/-- 有限段を経由する D の作用は、既存の `RPerfd` 上の D の作用と一致する。 -/
@[simp] theorem toRPerfd_algebraMap_D (n : ℕ) (d : D) :
    toRPerfd A D t p hperf n (algebraMap D (Section2.StageAlgebra A D t p n) d) =
      algebraMap D (RPerfd A D t p hperf) d :=
  (toRPerfd A D t p hperf n).commutes d


/-- 完備テンソル代数を経由する標準写像は、既存の有限段からの普遍写像と一致する。 -/
theorem stageToCompletedTensor_toMixedPerfectoid (n : ℕ) (x : Section2.StageAlgebra A D t p n) :
    toMixedPerfectoid A D t p hperf (Section2.stageToCompletedTensor A D t p n x) =
      toRPerfd A D t p hperf n x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    calc
      _ = toMixedPerfectoid A D t p hperf (Section2.stageToCompletedTensor A D t p n x) +
          toMixedPerfectoid A D t p hperf (Section2.stageToCompletedTensor A D t p n y) :=
        (congrArg (toMixedPerfectoid A D t p hperf)
          ((Section2.stageToCompletedTensor A D t p n).map_add x y)).trans
            ((toMixedPerfectoid A D t p hperf).map_add _ _)
      _ = toRPerfd A D t p hperf n x + toRPerfd A D t p hperf n y :=
        congrArg₂ (· + ·) hx hy
      _ = _ := ((toRPerfd A D t p hperf n).map_add x y).symm
  | tmul a d =>
    let : Algebra D (TowerStage A t p n ⊗[A] D) := Algebra.TensorProduct.rightAlgebra
    have hrhs : toRPerfd A D t p hperf n (a ⊗ₜ[A] d) =
        algebraMap D (RPerfd A D t p hperf) d * stageToRPerfd A D t p hperf n a := by
      change (Algebra.TensorProduct.lift (Algebra.ofId D (RPerfd A D t p hperf))
        (stageToRPerfd A D t p hperf n) (fun _ _ ↦ Commute.all _ _))
        ((Algebra.TensorProduct.commRight A D (TowerStage A t p n)).symm (a ⊗ₜ[A] d)) = _
      rw [Algebra.TensorProduct.commRight_symm_tmul, Algebra.TensorProduct.lift_tmul]
      rfl
    rw [hrhs, Section2.stageToCompletedTensor_tmul]
    calc
      _ = toMixedPerfectoid A D t p hperf (Section2.stageToCompletedTower A t p n a ⊗ₜ[A] (1 : D)) *
          toMixedPerfectoid A D t p hperf ((1 : CompletedTower A t p) ⊗ₜ[A] d) := by
        rw [← map_mul]
        congr 1
        simp
      _ = stageToRPerfd A D t p hperf n a * algebraMap D (RPerfd A D t p hperf) d := rfl
      _ = _ := mul_comm _ _

/-- 段写像の合成の一致を環準同型の等式として公開する。 -/
theorem toRPerfd_eq_toMixedPerfectoid_comp_stage (n : ℕ) :
    (toRPerfd A D t p hperf n).toRingHom =
      (toMixedPerfectoid A D t p hperf).comp (Section2.stageToCompletedTensor A D t p n).toRingHom := by
  apply RingHom.ext
  intro x
  exact (stageToCompletedTensor_toMixedPerfectoid A D t p hperf n x).symm

end SerrePositivity.CLMST
