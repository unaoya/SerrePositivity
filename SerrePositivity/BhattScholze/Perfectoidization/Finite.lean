module

public import SerrePositivity.BhattScholze.Perfectoidization.Interface.IntegralExistence
public import Mathlib.RingTheory.FinitePresentation
public import SerrePositivity.BhattScholze.PerfectoidIdeal.Basic

/-! # 有限代数の選んだ perfectoid 化

## 概要

integral perfectoid な `R` 上の有限表示な有限代数 `S` について、perfectoid 化の存在定理（`SerrePositivity.BhattScholze.exists_perfectoidization_of_finite`、BS 著者版 Theorem 1.17(1)）で保証される普遍対象を選び、環 `Perfectoidization R S p hR`、標準写像 `toPerfectoidization`、`S`・`R` の代数構造とその両立を与える。

## 方針

構成に長さやホモロジーの性質を組み込まず、存在定理が述べる普遍性だけを保つ。

## 規約

BhattScholze の整代数の存在定理を直接使い、普遍環とその単位を選ぶ。

## 使われ方

CLMST。
-/

@[expose] public noncomputable section

universe u

section PerfectoidizationPart

namespace SerrePositivity

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)

/-- 有限代数 `S` の perfectoid 化。存在定理で保証される普遍対象を選ぶ。 -/
noncomputable def Perfectoidization (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) : Type u :=
  (_root_.SerrePositivity.BhattScholze.exists_perfectoidization_of_finite R S p hR).choose

/-- 存在定理で選んだ普遍対象の環構造。 -/
noncomputable instance : CommRing (Perfectoidization R S p hR) :=
  (_root_.SerrePositivity.BhattScholze.exists_perfectoidization_of_finite R S p hR).choose_spec.choose

/-- 元の代数から perfectoid 化への標準写像。 -/
noncomputable def toPerfectoidization : S →+* Perfectoidization R S p hR :=
  (_root_.SerrePositivity.BhattScholze.exists_perfectoidization_of_finite R S p hR).choose_spec.choose_spec.choose

/-- 選んだ環と標準写像は perfectoid 化の普遍性を満たす。 -/
theorem isPerfectoidization_toPerfectoidization :
    IsPerfectoidization p (toPerfectoidization R S p hR) :=
  (_root_.SerrePositivity.BhattScholze.exists_perfectoidization_of_finite R S p hR).choose_spec.choose_spec.choose_spec

/-- 普遍写像による元の代数 `S` の作用。 -/
noncomputable instance : Algebra S (Perfectoidization R S p hR) :=
  (toPerfectoidization R S p hR).toAlgebra

/-- Perfectoid 化への標準写像は代数構造の写像である。 -/
theorem algebraMap_perfectoidization :
    algebraMap S (Perfectoidization R S p hR) = toPerfectoidization R S p hR := rfl

/-- `R → S` と普遍写像を合成した基底環の作用。 -/
noncomputable instance : Algebra R (Perfectoidization R S p hR) :=
  ((toPerfectoidization R S p hR).comp (algebraMap R S)).toAlgebra

/-- 基底環の作用と `S` の作用は合成の定義から両立する。 -/
instance : IsScalarTower R S (Perfectoidization R S p hR) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

end SerrePositivity

end PerfectoidizationPart
