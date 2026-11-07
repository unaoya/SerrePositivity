module

public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.BhattScholze.Perfectoidization.Finite
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.TensorProduct.Finite

/-! # 根の塔の完備化の上の perfectoid 化

## 概要

完備化した根の塔 `A∞` と有限代数 `D` から `C_D = (A∞ ⊗[A] D)_perfd`（`Section2.MixedPerfectoid`）を選び、標準写像 `toMixedPerfectoid` と、`A`・`D`・根の塔・完備化した塔の作用とその両立を与える。

## 方針

対象は有限代数の選んだ perfectoid 化（`Perfectoidization/Finite`、BS 著者版 Theorem 1.17(1) の存在定理に相対的）で、作用の両立は普遍性から示す。

## 規約

名前空間 `SerrePositivity.Section2` と宣言名は変えない（CLMST・Paper が多く参照する）。旧 `CLMST/Algebra` の基礎の部分（2a で BS の下へ移した）。CLMST の別名 `CLMST.RPerfd` は CLMST に残る。

## 使われ方

CLMST（`RPerfd`）、Paper/Section2/LengthAlgebra/MixedChar（Theorem 2.5 の混標数）。
-/

@[expose] public section
universe u
open scoped TensorProduct
namespace SerrePositivity.Section2

variable (A D : Type u) [CommRing A] [IsNoetherianRing A]
    [CommRing D] [Algebra A D] [Module.Finite A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)

/-- Noether 環上の有限加群は有限表示であり、perfectoid 化の存在定理を適用できる。 -/
local instance : Module.FinitePresentation A D := Module.finitePresentation_of_finite A D

/-- `C_D = (R∞ ⊗[A] D)_perfd`。 -/
abbrev MixedPerfectoid :=
  Perfectoidization (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D) p hperf

/-- 基底変更した有限代数から `C_D` への標準写像。 -/
noncomputable abbrev toMixedPerfectoid :
    (CompletedTower A t p) ⊗[A] D →+* MixedPerfectoid A D t p hperf :=
  toPerfectoidization (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D) p hperf

/-- `C_D` は perfectoid 化の普遍性を満たす。 -/
theorem isPerfectoidization_toMixedPerfectoid :
    IsPerfectoidization p (toMixedPerfectoid A D t p hperf) :=
  isPerfectoidization_toPerfectoidization _ _ _ _

/-- 完備化した塔を経由する基底環の作用。 -/
noncomputable instance mixedPerfectoidAlgebraA : Algebra A (MixedPerfectoid A D t p hperf) :=
  ((algebraMap (CompletedTower A t p) (MixedPerfectoid A D t p hperf)).comp
    (algebraMap A (CompletedTower A t p))).toAlgebra

/-- テンソル積の右側への包含と普遍写像による `D` の作用。 -/
noncomputable instance mixedPerfectoidAlgebraD : Algebra D (MixedPerfectoid A D t p hperf) :=
  ((toMixedPerfectoid A D t p hperf).comp Algebra.TensorProduct.includeRight.toRingHom).toAlgebra

/-- 完備化した塔を経由する、完備化前の塔の作用。 -/
noncomputable instance mixedPerfectoidAlgebraTower :
    Algebra (Tower A t p) (MixedPerfectoid A D t p hperf) :=
  ((algebraMap (CompletedTower A t p) (MixedPerfectoid A D t p hperf)).comp
    (algebraMap (Tower A t p) (CompletedTower A t p))).toAlgebra

/-- 基底環から完備化した塔を経由する作用の両立。 -/
instance mixedPerfectoidScalarTowerCompleted :
    IsScalarTower A (CompletedTower A t p) (MixedPerfectoid A D t p hperf) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- 完備化前後の塔の作用は両立する。長さの係数制限に使う。 -/
instance mixedPerfectoidScalarTowerTowerCompleted :
    IsScalarTower (Tower A t p) (CompletedTower A t p) (MixedPerfectoid A D t p hperf) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- 基底環と完備化前の塔の作用は両立する。 -/
instance mixedPerfectoidScalarTowerTower :
    IsScalarTower A (Tower A t p) (MixedPerfectoid A D t p hperf) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- テンソル積の両側で基底環の像は一致するので、`A` と `D` の作用は両立する。 -/
instance mixedPerfectoidScalarTowerD :
    IsScalarTower A D (MixedPerfectoid A D t p hperf) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change toMixedPerfectoid A D t p hperf
    (algebraMap (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D)
      (algebraMap A (CompletedTower A t p) a)) =
    toMixedPerfectoid A D t p hperf (Algebra.TensorProduct.includeRight (algebraMap A D a))
  rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

end SerrePositivity.Section2
