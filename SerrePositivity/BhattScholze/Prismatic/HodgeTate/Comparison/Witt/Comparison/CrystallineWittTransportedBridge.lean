module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.AffineCechPointwiseCoefficients
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDCompletedCoefficientComplex
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittPointwiseBridge
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridgeComplex
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridge
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittCrystallinePrism
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseTensor

/-!
# 整係数の結晶の橋を Witt 模型に移した擬同型

## 概要
整係数の橋の各項の完備係数拡大を、実際の Witt affine 模型と分冪模型の間に移す。

## 方針
両側の余単体的な完備係数比較を交代余面複体へ移し、既存の平坦な係数拡大の擬同型を挟む。

## 規約
このファイルは比較同型によって移した射を固定する。指定された Witt の環射との照合は別に行う。

## 使われ方
BS 著者版 Theorem 6.4、結晶の橋の厳密な比較。
-/

public noncomputable section
open CategoryTheory AlgebraicTopology
open SerrePositivity.DerivedCompletion
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (C : Type u) [CommRing C]
variable (hpC : Function.Injective (fun x : C => (p : C) * x))
variable [IsAdicComplete (Ideal.span {(p : C)}) C] (r : ℕ)
local notation "k" => crystallineBase p
local notation "W" => WittVector p C
local notation "Q" => wittCrystallinePrism hpC
local notation "hQ" => crystallineBounded p Q rfl
local notation "f" => crystallineWittBaseMap p C hpC
local notation "F" => pCompletedScalarExtensionFunctor p f

/-- Witt 結晶基底上の実際の有限 affine 交代余面複体。 -/
def crystallineWittAffineComplex : CochainComplex (ModuleCat.{u} W) ℕ :=
  (alternatingCofaceMapComplex (ModuleCat W)).obj
    (SerrePositivity.Cosimplicial.toModules W (htRings Q hQ r) (htBase Q hQ r))

/-- Witt 係数の実際の小さい分冪交代余面複体。 -/
def crystallineWittPDComplex : CochainComplex (ModuleCat.{u} W) ℕ :=
  (alternatingCofaceMapComplex (ModuleCat W)).obj
    (SerrePositivity.Cosimplicial.toModules W (pdCechRings p W r) (pdCechBase p W r))

/-- 整係数 affine 複体の各項の完備係数拡大を、Witt affine 複体に同定する。 -/
def crystallineWittAffineComplexIso :
    ((F).mapHomologicalComplex _).obj (crystallineSmallSourceComplex.{u} p r) ≅
      crystallineWittAffineComplex p C hpC r := by
  let Z := crystallineBasePrism.{u} p
  let hZ := crystallineBaseBounded.{u} p
  exact (SerrePositivity.Cosimplicial.alternatingCofaceMapComplexCompMapHomologicalComplexIso
      (F)).app (SerrePositivity.Cosimplicial.toModules k (htRings Z hZ r) (htBase Z hZ r)) ≪≫
    (alternatingCofaceMapComplex (ModuleCat W)).mapIso
      (affineCechPointwiseCoefficientIso Z Q hZ hQ rfl (crystallineWittBaseHom p C hpC) r)

/-- 整係数分冪複体の各項の完備係数拡大を、Witt 分冪複体に同定する。 -/
def crystallineWittPDComplexIso :
    ((F).mapHomologicalComplex _).obj (crystallineSmallTargetComplex.{u} p r) ≅
      crystallineWittPDComplex p C r := by
  let : Algebra (crystallineBase.{u} p) W := (f).toAlgebra
  exact pdCompletedCoefficientComplexIso p (crystallineBase.{u} p) W r

/-- 実際の二つの Witt 模型に、整係数の橋を比較同型で移した射。 -/
def crystallineWittTransportedBridge :
    crystallineWittAffineComplex p C hpC r ⟶ crystallineWittPDComplex p C r :=
  (crystallineWittAffineComplexIso p C hpC r).inv ≫
    ((F).mapHomologicalComplex _).map (crystallineSmallBridgeCochainMap.{u} p r) ≫
      (crystallineWittPDComplexIso p C hpC r).hom

/-- 比較同型で移した Witt の橋は擬同型。 -/
theorem crystallineWittTransportedBridge_quasiIso :
    QuasiIso (crystallineWittTransportedBridge p C hpC r) := by
  have h := crystallineWittPointwiseBridge_quasiIso p r C hpC
  change QuasiIso (((ModuleCat.extendScalars (f) ⋙
      moduleCompletionH0Functor W ((f) (p : crystallineBase.{u} p))).mapHomologicalComplex _).map
        (crystallineSmallBridgeCochainMap.{u} p r)) at h
  rw [map_natCast] at h
  let : QuasiIso (((F).mapHomologicalComplex _).map (crystallineSmallBridgeCochainMap.{u} p r)) := h
  dsimp only [crystallineWittTransportedBridge]
  infer_instance

end SerrePositivity.BhattScholze.Prismatic
