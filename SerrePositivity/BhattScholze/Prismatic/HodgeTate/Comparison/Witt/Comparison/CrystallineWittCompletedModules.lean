module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittFlat
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridgeQuasiIso
public import SerrePositivity.HomologicalAlgebra.CompletedFlatRegularModule
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridgeComplex
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridgeQuasiIso
import all SerrePositivity.HomologicalAlgebra.RestrictedBaseChangeComplex

/-!
# p 正則加群の Witt 係数への完備導来底変換

## 概要
結晶基底上の p 正則加群を Witt 係数へ完備導来底変換すると、次数 0 に集中する。

## 方針
標準の係数射の平坦性と、既存の正則加群の完全平坦な完備底変換の純性を使う。

## 規約
Witt 係数の C は p 正則かつ p 進完備。加群の p 正則性を仮定に明記する。
この段では H⁰ の環としての同定を主張しない。

## 使われ方
BS 著者版 Theorem 6.4 の古典的な各項の完備テンソルと導来底変換の照合。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (C : Type u) [CommRing C]
variable (hpC : Function.Injective (fun x : C => (p : C) * x))
variable [IsAdicComplete (Ideal.span {(p : C)}) C]

local notation "k" => crystallineBase p
local notation "W" => WittVector p C
local notation "f" => crystallineWittBaseMap p C hpC

/-- 標準の Witt 係数加群は (p) 完全平坦。 -/
theorem crystallineWittBase_completelyFlat :
    IsCompletelyFlat (Ideal.span {(p : crystallineBase.{u} p)}) (baseChangeScalarModule (f)) := by
  let : Algebra (crystallineBase.{u} p) W := (f).toAlgebra
  have hF : Module.Flat (crystallineBase.{u} p) W := crystallineWittBaseMap_flat p C hpC
  let : Module.Flat (crystallineBase.{u} p) (baseChangeScalarModule (f)) := hF
  intro N _ _ _
  apply (isConcentratedInDegreeZero_derivedTensor_iff (baseChangeScalarModule (f)) N).mpr
  intro i hi
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  exact torModule_subsingleton_of_flat (baseChangeScalarModule (f)) N j

/-- p 正則加群の Witt 係数への完備導来底変換は、p 正則な H⁰ のみに集中する。 -/
theorem crystallineWittCompletedModule_pure (M : ModuleCat.{u} (crystallineBase.{u} p))
    (hM : IsSMulRegular M (p : crystallineBase.{u} p)) :
    let Y := (derivedComplexCompletionFunctor W (p : W)).obj
      ((boundedAboveDerivedBaseChange (f)).obj (boundedAboveDerivedSingleFunctor.obj M)).obj
    Y.IsGE 0 ∧ Y.IsLE 0 ∧ Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat W) 0).obj Y => (p : W) • x) := by
  have h := completedBaseChange_regular_module_pure
    (f) (p : crystallineBase.{u} p) (crystallineWittBase_completelyFlat p C hpC) M hM
  rw [map_natCast (crystallineWittBaseMap.{u} p C hpC)] at h
  exact h

/-- 離散性により、完備導来底変換は実際の H⁰ の single 対象と同型。 -/
def crystallineWittCompletedModuleIso (M : ModuleCat.{u} (crystallineBase.{u} p))
    (hM : IsSMulRegular M (p : crystallineBase.{u} p)) :
    let Y := (derivedComplexCompletionFunctor W (p : W)).obj
      ((boundedAboveDerivedBaseChange (f)).obj (boundedAboveDerivedSingleFunctor.obj M)).obj
    Y ≅ (DerivedCategory.singleFunctor (ModuleCat W) 0).obj
      ((DerivedCategory.homologyFunctor (ModuleCat W) 0).obj Y) := by
  have h := crystallineWittCompletedModule_pure p C hpC M hM
  let := h.1
  let := h.2.1
  exact normalizedPureHomologyIso _ 0

end SerrePositivity.BhattScholze.Prismatic
