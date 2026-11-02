module

public import SerrePositivity.BhattScholze.Perfectoidization.RootTower

/-! # CLMST の `RPerfd`

## 概要

`RPerfd A D t p hperf` は、根の塔の完備化の上の perfectoid 化 `(A∞ ⊗[A] D)_perfd`（`Section2.MixedPerfectoid`、BhattScholze/Perfectoidization/RootTower）の透明な別名。

## 規約

別の存在の選択は行わず、代数の作用と定義上の等式をそのまま使う。テンソル積の順序は `A∞ ⊗[A] D`（原典は `D ⊗[A] A∞`）。

## 使われ方

CLMST の全体。
-/

@[expose] public section

universe u

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
