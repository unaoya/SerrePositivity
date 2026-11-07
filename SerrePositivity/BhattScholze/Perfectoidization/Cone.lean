module

public import SerrePositivity.BhattScholze.Perfectoidization.Finite
public import SerrePositivity.HomologicalAlgebra.DerivedModuleCone

/-! # perfectoid 化の標準写像の導来錐

## 概要

選んだ普遍 perfectoid 環への標準写像を `R` 線形写像（`perfectoidizationModuleMap`）にし、零次の加群写像の写像錐を導来圏へ送った錐 `perfectoidizationCone` と、その完全三角形を与える。
BS 著者版 Corollary 8.12 の excision の環版に使う、標準写像の導来錐を比較する。

## 方針

錐を未知の述語として仮定せず、Mathlib の写像錐から作る。

## 規約

perfectoid 化の存在の入力に相対的な構成で、新しい perfectoid 化は選ばない。旧 `CLMST/PerfectoidizationCone`。

## 使われ方

CLMST の Prop 2.4.7（同種性の主張は錐の零化として述べる）。
-/

@[expose] public noncomputable section

universe u

section PerfectoidizationConePart

namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Pretriangulated
attribute [local instance] HasDerivedCategory.standard

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)

/-- 普遍 perfectoid 化への標準写像を、元の基底 R 上の線形写像として扱う。 -/
def perfectoidizationModuleMap : S →ₗ[R] Perfectoidization R S p hR :=
  (IsScalarTower.toAlgHom R S (Perfectoidization R S p hR)).toLinearMap

/-- 線形写像の値は、選んだ perfectoid 化への既存の標準写像と同じ。 -/
@[simp] theorem perfectoidizationModuleMap_apply (s : S) :
    perfectoidizationModuleMap R S p hR s = toPerfectoidization R S p hR s := rfl

/-- 標準写像 S[0]→S_perfd[0] の、実導来圏 D(R) での錐。 -/
abbrev perfectoidizationCone : DerivedCompletion.ConcreteDerivedCategory R :=
  moduleMapCone R (perfectoidizationModuleMap R S p hR)

/-- 標準写像とその錐の実際の完全三角形。 -/
abbrev perfectoidizationTriangle : Triangle (DerivedCompletion.ConcreteDerivedCategory R) :=
  moduleMapConeTriangle R (perfectoidizationModuleMap R S p hR)

/-- 標準写像と錐の三角形は、実導来圏で distinguished である。 -/
theorem perfectoidizationTriangle_distinguished :
    perfectoidizationTriangle R S p hR ∈
      distTriang (DerivedCompletion.ConcreteDerivedCategory R) :=
  moduleMapConeTriangle_distinguished R (perfectoidizationModuleMap R S p hR)

/-- 標準三角形の第三対象は、定義した実導来錐そのものである。 -/
@[simp] theorem perfectoidizationTriangle_obj₃ :
    (perfectoidizationTriangle R S p hR).obj₃ = perfectoidizationCone R S p hR := rfl

end SerrePositivity.BhattScholze

end PerfectoidizationConePart
