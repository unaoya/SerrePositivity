module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittFlat
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridgeQuasiIso
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseCochain
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridgeComplex
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridgeQuasiIso
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra

/-!
# 各項を完備係数拡大した小さい結晶の橋

## 概要
整係数の実際の小さい結晶の橋は、各項の Witt 係数拡大と H⁰ 主完備化の後も擬同型。

## 方針
もとの二複体の各項で p が正則であることを確認し、
平坦な各項完備係数拡大の擬同型保存を適用する。

## 規約
係数環 C は p 正則かつ p 進完備。実際の余鎖射を指定し、整数添字への変更はしない。

## 使われ方
BS 著者版 Theorem 6.4 の最初の Witt 比較への整係数の橋の移送。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

/-- 整係数の affine 複体の各項では p の作用は単射。 -/
theorem crystallineSmallSourceTerm_regular (n : ℕ) :
    IsSMulRegular ((crystallineSmallSourceComplex.{u} p r).X n) (p : crystallineBase.{u} p) := by
  change Function.Injective (fun x : (zpCech.{u} p r).obj ⦋n⦌ =>
    ((htBase (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r).app ⦋n⦌).hom
      (p : crystallineBase.{u} p) * x)
  simpa only [htGenerator, crystallineBase_generator] using
    htGenerator_regular (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r ⦋n⦌

/-- 整係数の小さい分冪複体の各項では p の作用は単射。 -/
theorem crystallineSmallTargetTerm_regular (n : ℕ) :
    IsSMulRegular ((crystallineSmallTargetComplex.{u} p r).X n) (p : crystallineBase.{u} p) := by
  change Function.Injective (fun x : (pdRings.{u} p r).obj ⦋n⦌ =>
    ((pdCechBase p (crystallineBase.{u} p) r).app ⦋n⦌).hom (p : crystallineBase.{u} p) * x)
  rw [map_natCast ((pdCechBase p (crystallineBase.{u} p) r).app ⦋n⦌).hom]
  exact y_regular.{u} p r ⦋n⦌

variable (C : Type u) [CommRing C]
variable (hpC : Function.Injective (fun x : C => (p : C) * x))
variable [IsAdicComplete (Ideal.span {(p : C)}) C]

/-- 実際の小さい結晶の橋は、各項の完備 Witt 係数拡大の後も擬同型。 -/
theorem crystallineWittPointwiseBridge_quasiIso :
    QuasiIso
      (((pointwiseCompletedBaseChangeFunctor (p : crystallineBase.{u} p)
        (crystallineWittBaseMap p C hpC)).mapHomologicalComplex (.up ℕ)).map
          (crystallineSmallBridgeCochainMap.{u} p r)) := by
  exact pointwiseCompletedBaseChangeNat_quasiIso_of_flat_of_regular
    (p : crystallineBase.{u} p) (crystallineWittBaseMap p C hpC)
    (crystallineWittBaseMap_flat p C hpC) (crystallineSmallBridgeCochainMap.{u} p r)
    (crystallineSmallSourceTerm_regular.{u} p r) (crystallineSmallTargetTerm_regular.{u} p r)
    (crystallineSmallBridgeCochainMap_quasiIso.{u} p r)

end SerrePositivity.BhattScholze.Prismatic
