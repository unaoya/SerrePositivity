module

public import SerrePositivity.Paper.Section2.CompletedTower
public import SerrePositivity.CommutativeAlgebra.Perfectoidization
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.TensorProduct.Finite

/-! # 混標数の長さ代数の台となる perfectoid 環

完備化した根の塔を `R∞` とし、`R∞ ⊗[A] D` の perfectoid 化を取る。
`A` 上有限な `D` は有限表示でもあり、基底変更後の有限性・有限表示性は Mathlib から従う。
存在のみを引用した普遍対象に、`A`・`D`・根の塔の両立する作用を定義する。
この段階では長さの消滅や重複度の公式は使わない。
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
