module

public import SerrePositivity.BhattScholze.Perfectoidization.RootTower
public import SerrePositivity.CommutativeAlgebra.RootTower.BaseChange

/-! # CLMST の `RPerfd` と有限段からの写像

## 概要

`RPerfd A D t p hperf` は、根の塔の完備化の上の perfectoid 化 `(A∞ ⊗[A] D)_perfd`（`Section2.MixedPerfectoid`、BhattScholze/Perfectoidization/RootTower）の透明な別名。有限段の基底変更 `Section2.StageAlgebra`（CommutativeAlgebra/RootTower/BaseChange）から `RPerfd` への標準の `D` 代数写像 `toRPerfd` を作り、`D` の作用との両立と、完備テンソル積を経由する `toMixedPerfectoid` との一致を示す。

## 方針

別の存在の選択は行わず、代数の作用と定義上の等式をそのまま使う。

## 規約

CLMST の記号 `R_perfd`（Notation 4.0.1）。テンソル積の順序は `A∞ ⊗[A] D`（原典は `D ⊗[A] A∞`）。旧 `CLMST/Algebra`・`StageRPerfd`。

## 使われ方

CLMST の全体。
-/

@[expose] public noncomputable section

universe u

section AlgebraPart

open scoped TensorProduct

namespace SerrePositivity.CLMST

variable (A D : Type u) [CommRing A] [IsNoetherianRing A]
    [CommRing D] [Algebra A D] [Module.Finite A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (Section2.CompletedTower A t p) p)

/-- CLMST の `RPerfd`：既存の選択による `(A∞ ⊗[A] D)_perfd` の透明な別名。
別の存在選択は行わず、既存の代数作用と定義的等式をそのまま再利用する。 -/
abbrev RPerfd := Section2.MixedPerfectoid A D t p hperf

end SerrePositivity.CLMST

end AlgebraPart

section StageRPerfdPart

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

end StageRPerfdPart
