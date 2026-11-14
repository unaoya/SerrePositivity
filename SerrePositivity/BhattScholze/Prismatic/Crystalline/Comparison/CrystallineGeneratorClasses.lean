module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCoordinateReduction
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamComparisonClass
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineChainProduct
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.FinitePolynomialCartier
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateOneDerivative
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateOneDerivative
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateOneGenerators
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCoordinateReduction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineTotalCoordinate
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineChain
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBockstein
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateZero
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.CohomologyZero
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCohomology

/-!
# Hodge–Tate と Cartier の生成元

## 概要
結晶比較に沿って零次の座標と一次の微分を inverse Cartier の生成元に送る。

## 方針
整係数で割った微分の剰余を同じ総複体の余輪体として取り、二つの射影で読む。

## 規約
一次の Bockstein は第 1 頂点から第 0 頂点を引いた余面微分で計算する。

## 使われ方
結晶基底上の多項式 Hodge–Tate 同型。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial SerrePositivity.DeRham
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "C" => pdRings p r
local notation "k" => cartierBase p

private def pdPrimeQuotient :
    pdRings.{u} p r ⟶ modPrimeCosimplicial p (pdRings.{u} p r) :=
  quotProjection (pdRings.{u} p r) (fun n => (p : (pdRings.{u} p r).obj n))
    (fun θ => map_natCast ((pdRings.{u} p r).map θ).hom p) 1

set_option backward.isDefEq.respectTransparency false in
private def pdCoordinateCocycleZero (j : Fin r) (y : (pdRings.{u} p r).obj ⦋1⦌)
    (hy : cochainDifferential (pdRings.{u} p r) 0 (pdCoordinateLift p r j ^ p) =
      (p : (pdRings.{u} p r).obj ⦋1⦌) * y) :
    Cocycles (modPrimeCosimplicial p (pdRings.{u} p r)) 0 :=
  ⟨(pdPrimeQuotient p r).app ⦋0⦌ (pdCoordinateLift p r j ^ p), by
    change (ringCochainComplex (modPrimeCosimplicial p (pdRings.{u} p r))).d 0 1
      ((pdPrimeQuotient p r).app ⦋0⦌ (pdCoordinateLift p r j ^ p)) = 0
    rw [ringCochainComplex_d_apply, ← cochainDifferential_natural _ _ (pdPrimeQuotient p r),
      hy, map_mul]
    have h : (pdPrimeQuotient p r).app ⦋1⦌ (p : (pdRings.{u} p r).obj ⦋1⦌) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [pow_one]
      exact Ideal.subset_span rfl
    rw [h, zero_mul]⟩

set_option backward.isDefEq.respectTransparency false in
private def pdCoordinateCocycleOne (j : Fin r) (y : (pdRings.{u} p r).obj ⦋1⦌)
    (hy : cochainDifferential (pdRings.{u} p r) 0 (pdCoordinateLift p r j ^ p) =
      (p : (pdRings.{u} p r).obj ⦋1⦌) * y) :
    Cocycles (modPrimeCosimplicial p (pdRings.{u} p r)) 1 :=
  projectCycle C (fun n => (p : (pdRings.{u} p r).obj n))
    (fun θ => map_natCast ((pdRings.{u} p r).map θ).hom p) 1 y
    (cochainDifferential_eq_zero_of_eq_mul C (fun n => (p : (pdRings.{u} p r).obj n))
      (fun θ => map_natCast ((pdRings.{u} p r).map θ).hom p) (pdRings_p_regular p r) 0 _ _ hy)

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- 結晶比較の次数 0・1 の生成元における値。 -/
theorem crystallineChain_generators (j : Fin r) :
    let Z := crystallineBasePrism.{u} p
    let hZ := crystallineBaseBounded.{u} p
    let c := finitePolynomialCartier.{u} p r
    crystallineChain p r 0 (hodgeTateMapZero Z hZ r (prismPolynomialUnit Z (Fin r) (MvPolynomial.X j))) =
      c.app 0 (formsZeroEquiv _ _ (MvPolynomial.X (ULift.up j))) ∧
    crystallineChain p r 1 (hodgeTateMapOne Z hZ r
      (completedFormsUnit _ _ p 1 (dX _ _ (ULift.up j)))) = c.app 1 (dX _ _ (ULift.up j)) := by
  dsimp only
  obtain ⟨y, hy⟩ := pdFrobCoordinate_horizontal_dvd.{u} p r j
  let f := crystallineBridgeModP_isCohomologyIso.{u} p r
  let g := pdInclusionModP_isCohomologyIso.{u} p r
  let e := isCohomologyIso_of_isIso (pdModel_modP.{u} p r).hom
  let w := pdDeRhamCechToPolynomial p (cartierBase.{u} p) r (cartierBase_natCast p)
  let a := pdCoordinateCocycleZero p r j y hy
  let b := pdCoordinateCocycleOne p r j y hy
  let x := prismPolynomialUnit (crystallineBasePrism.{u} p) (Fin r) (MvPolynomial.X j)
  let η₀ := hodgeTateMapZero (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r x
  let X' := reducedModel (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r
  let a' := zeroCocyclesEquiv X' (htSecZero (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r x)
  have hzero : f.addEquiv 0 η₀ = g.addEquiv 0 (cohomologyClass _ 0 a) := by
    change cohomologyMap X' _ (crystallineBridgeModP p r) 0 (cohomologyClass X' 0 a') =
      cohomologyMap _ _ (pdInclusionModP p r) 0 (cohomologyClass _ 0 a)
    rw [cohomologyMap_class, cohomologyMap_class]
    congr 1
    apply Subtype.ext
    exact crystallineBridge_coordinate p r j
  have hβ : pdModelBockstein p r 0 (cohomologyClass _ 0 a) = cohomologyClass _ 1 b :=
    cupBockstein_class C (fun n => (p : (pdRings.{u} p r).obj n))
      (fun θ => map_natCast ((pdRings.{u} p r).map θ).hom p) (pdRings_p_regular p r) (crystallineBase.{u} p)
      (pdCechBase p (crystallineBase.{u} p) r) 0 a b (pdCoordinateLift p r j ^ p) y rfl rfl hy
  have hone : f.addEquiv 1 (bockstein (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r 0 η₀) =
      g.addEquiv 1 (cohomologyClass _ 1 b) := by
    have h := crystallineBridgeModP_bockstein p r 0 η₀
    change f.addEquiv 1 (bockstein _ _ r 0 η₀) = pdDeltaBockstein p r 0 (f.addEquiv 0 η₀) at h
    rw [h, hzero]
    have h' := pdInclusionModP_bockstein p r 0 (cohomologyClass _ 0 a)
    change g.addEquiv 1 (pdModelBockstein p r 0 (cohomologyClass _ 0 a)) =
      pdDeltaBockstein p r 0 (g.addEquiv 0 (cohomologyClass _ 0 a)) at h'
    rw [← h', hβ]
  let c := finitePolynomialCartier.{u} p r
  let T := formVars.{u} r
  let t : T := ULift.up j
  constructor
  · change w 0 (e.addEquiv 0 ((g.addEquiv 0).symm (f.addEquiv 0 η₀))) =
      c.app 0 (formsZeroEquiv k T (MvPolynomial.X t))
    rw [hzero, AddEquiv.symm_apply_apply, c.on_zero]
    change w 0 (cohomologyMap _ _ (pdModel_modP p r).hom 0 (cohomologyClass _ 0 a)) = _
    rw [cohomologyMap_class]
    exact pdDeRhamCechToPolynomial_class p (cartierBase.{u} p) r (cartierBase_natCast p) 0
      (reducedCoordinateZero p r j) (reducedCoordinateZero_closed p r j) _
      (formsZeroEquiv k T ((MvPolynomial.X t) ^ p)) (cartierZero_closed k T p (cartierBase_natCast p) _)
      (reducedCoordinateZero_row p r j) (reducedCoordinateZero_column p r j)
  · have hη : hodgeTateMapOne (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r
        (completedFormsUnit k T p 1 (dX k T t)) =
        bockstein (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r 0 η₀ :=
      by
        change htOneOnGenerators (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r
          (affineCoordinateFormOne (crystallineBasePrism.{u} p) r j) = _
        exact htOneOnGenerators_coordinate (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r j
    rw [hη]
    change w 1 (e.addEquiv 1 ((g.addEquiv 1).symm (f.addEquiv 1
      (bockstein (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r 0 η₀)))) =
        c.app 1 (dX k T t)
    rw [hone, AddEquiv.symm_apply_apply, c.on_one]
    change w 1 (cohomologyMap _ _ (pdModel_modP p r).hom 1 (cohomologyClass _ 1 b)) = _
    rw [cohomologyMap_class]
    exact pdDeRhamCechToPolynomial_class p (cartierBase.{u} p) r (cartierBase_natCast p) 1
      (reducedCoordinateOne p r j y) (reducedCoordinateOne_closed p r j y hy) _
      (((MvPolynomial.X t : Poly k T) ^ (p-1)) • dX k T t) (cartierOne_closed k T p t)
      (reducedCoordinateOne_row p r j y) (reducedCoordinateOne_column p r j y)

end SerrePositivity.BhattScholze.Prismatic
