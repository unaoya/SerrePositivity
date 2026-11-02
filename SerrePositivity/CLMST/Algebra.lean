module

public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.BhattScholze.Perfectoidization.Finite
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.TensorProduct.Finite

/-! # CLMST で用いる根の塔上の perfectoid 化

完備化した根の塔 `A∞` と有限代数 `D` から `(A∞ ⊗[A] D)_perfd` を選び、
`A`・`D`・根の塔・完備化した塔の作用と、その両立を構成する。
このモジュールは `Paper/`、正規化長さ、CLMST の長さやホモロジーの引用を import しない。

対象の存在は `Inputs.exists_perfectoidization_of_finite`（現行引用在庫の Input 8）に依存する。
この有限代数版は、Bhatt–Scholze Theorem 1.17(1) の整代数の存在引用から証明して導く。
存在引用そのものを証明済みとは扱わない。
普遍性で選んだ環への作用の整合性は、その存在引用に相対的に証明済みである。

既存の `SerrePositivity.Section2` の宣言名・定義・証明を保持する。
`CLMST.RPerfd` は同じ選択を再利用する透明な別名で、テンソル積の順序も
既存の `A∞ ⊗[A] D` と一致させる。原典の `D ⊗[A] A∞` との交換同型と
同じ perfectoid 化への普遍写像・D の作用の比較は `CLMST/TensorOrder.lean` で証明する。
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

namespace SerrePositivity.CLMST

variable (A D : Type u) [CommRing A] [IsNoetherianRing A]
    [CommRing D] [Algebra A D] [Module.Finite A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (Section2.CompletedTower A t p) p)

/-- CLMST の `RPerfd`：既存の選択による `(A∞ ⊗[A] D)_perfd` の透明な別名。
別の存在選択は行わず、既存の代数作用と定義的等式をそのまま再利用する。 -/
abbrev RPerfd := Section2.MixedPerfectoid A D t p hperf

end SerrePositivity.CLMST
