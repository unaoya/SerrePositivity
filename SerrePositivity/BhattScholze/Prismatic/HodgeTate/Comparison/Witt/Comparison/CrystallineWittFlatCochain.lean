module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittFlat
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridgeQuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# 整係数の小さい橋の平坦な Witt 係数変更

## 概要
整係数の実際の小さい橋は、通常の Witt 係数拡大と複体全体の導来 p 完備化の後でも可逆。

## 方針
標準の係数射の平坦性により通常の係数拡大はホモロジーを保つ。
既存の小さい橋の擬同型を写し、導来完備化を適用する。

## 規約
この段では、完備化した複体と各項を完備化した複体との同定は使わない。

## 使われ方
BS 著者版 Theorem 6.4 の整係数から Witt 結晶基底への比較。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime] (C : Type u) [CommRing C]
variable (hpC : Function.Injective (fun x : C => (p : C) * x))
variable [IsAdicComplete (Ideal.span {(p : C)}) C] (r : ℕ)

local notation "W" => WittVector p C
local notation "f" => crystallineWittBaseMap p C hpC

/-- 整係数の小さい橋の通常の Witt 係数拡大は擬同型。 -/
theorem crystallineWittOrdinaryBridge_quasiIso :
    QuasiIso (((ModuleCat.extendScalars (f)).mapHomologicalComplex (.up ℕ)).map
      (crystallineSmallBridgeCochainMap.{u} p r)) := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (crystallineWittBaseMap_flat p C hpC)
  have := crystallineSmallBridgeCochainMap_quasiIso.{u} p r
  infer_instance

/-- 複体全体を導来 p 完備化しても、通常の Witt 係数拡大した小さい橋は可逆。 -/
theorem crystallineWittCompletedBridge_isIso :
    IsIso ((derivedComplexCompletionFunctor W (p : W)).map
      (DerivedCategory.Q.map
        (((ModuleCat.extendScalars (f)).mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.extendMap (crystallineSmallBridgeCochainMap.{u} p r)
            ComplexShape.embeddingUpNat)))) := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (crystallineWittBaseMap_flat p C hpC)
  have := crystallineSmallBridgeCochainMap_quasiIso.{u} p r
  have : QuasiIso (HomologicalComplex.extendMap (crystallineSmallBridgeCochainMap.{u} p r)
      ComplexShape.embeddingUpNat) := inferInstance
  have : QuasiIso (((ModuleCat.extendScalars (f)).mapHomologicalComplex (.up ℤ)).map
      (HomologicalComplex.extendMap (crystallineSmallBridgeCochainMap.{u} p r)
        ComplexShape.embeddingUpNat)) := inferInstance
  infer_instance

end SerrePositivity.BhattScholze.Prismatic
