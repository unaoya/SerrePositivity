module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseHodgeTateMap
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineCohomologyClasses
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseHodgeTateMap
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBasePolynomialAction
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineCohomologyClasses
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.AffineCochainModel

/-!
# 元の多項式係数と基底係数の同じコホモロジー類

## 概要
元の多項式係数の作用を基底へ制限したホモロジー同型は、元の同じ剰余余輪体を運ぶ。

## 方針
完全な係数制限の元の射影式と、元の係数複体の恒等成分を使う。

## 規約
標準HT写像も、元のコホモロジーとの同一視も変えない。

## 使われ方
元のHT実現を、同じ基底係数の余輪体の計算へ戻す。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open SerrePositivity.Cosimplicial HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

set_option maxHeartbeats 800000 in
/-- 元の多項式作用を制限した同型は、元の剰余余輪体の同じ類を与える。 -/
theorem affineBasePolynomialCohomologyIso_cohomology (i : ℕ)
    (z : hodgeTateCohomology' P hP r i) :
    (affineBasePolynomialCohomologyIso P hP r i).hom
        (affineHTCohomologyEquiv P hP r i z) =
      affineNativeBaseCohomologyEquiv P hP r i z := by
  let U := ModuleCat.restrictScalars (affineBaseToPolynomialMap P r)
  let K := affineHTComplex P hP r
  let L := affineBaseComplex P hP r
  let KU := (U.mapHomologicalComplex (.up ℕ)).obj K
  let e := affineBasePolynomialComplexIso P hP r
  obtain ⟨c, rfl⟩ := cohomologyClass_surjective (reducedModel P hP r) i z
  let cP := affineHTCycleRep P hP r i c
  let cA := moduleCycleRep A (reducedModel P hP r) (affineBaseCoefficients P hP r) i c
  let v := ((K.sc i).mapCyclesIso U).inv cP
  have hv : cyclesMap e.hom i v = cA := by
    apply (ModuleCat.mono_iff_injective (L.iCycles i)).mp inferInstance
    have h₁ := ConcreteCategory.congr_hom (cyclesMap_i e.hom i) v
    have h₂ := ConcreteCategory.congr_hom (coefficientCyclesIso_inv_inclusion (K.sc i) U) cP
    change L.iCycles i (cyclesMap e.hom i v) = e.hom.f i (KU.iCycles i v) at h₁
    change KU.iCycles i v = K.iCycles i cP at h₂
    rw [h₁, h₂, affineHTCycleRep_i, moduleCycleRep_apply]
    rfl
  have hp := ConcreteCategory.congr_hom (coefficientHomologyIso_inv_projection (K.sc i) U) cP
  change ((K.sc i).mapHomologyIso U).inv (K.homologyπ i cP) = KU.homologyπ i v at hp
  rw [affineHTCohomologyEquiv_class, affineNativeBaseCohomologyEquiv_class]
  change homologyMap e.hom i (((K.sc i).mapHomologyIso U).inv (K.homologyπ i cP)) =
    L.homologyπ i cA
  rw [hp]
  have h := ConcreteCategory.congr_hom (homologyπ_naturality e.hom i) v
  change homologyMap e.hom i (KU.homologyπ i v) = L.homologyπ i (cyclesMap e.hom i v) at h
  exact h.trans (congrArg (L.homologyπ i) hv)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
