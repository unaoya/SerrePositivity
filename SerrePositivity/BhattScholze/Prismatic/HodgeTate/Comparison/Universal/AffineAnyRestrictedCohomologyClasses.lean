module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedBaseRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineCohomologyClasses
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedBaseRows
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineBaseCoefficientModels
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.AffineCrystallineCohomologyClasses

/-!
# 向き付き係数射の元の余輪体の類

## 概要
元の係数制限への余鎖射が、同じ剰余係数射のコホモロジー写像を与えることを示す。

## 方針
元の余輪体を核へ入れ、完全な係数制限の標準ホモロジー同型の射影式を使う。

## 規約
生成元がpのときに限らず、平坦性も仮定しない。

## 使われ方
通常係数拡大の単位の正方形を、元の標準HT類の係数変更と照合する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory AlgebraicTopology HomologicalComplex
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open SerrePositivity.Cosimplicial HTComparisonTotal HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (r : ℕ)

/-- 同じ元の係数射を、元の基底係数複体の係数制限への射として読む。 -/
def affineAnyBaseRestrictedComplexMap :
    affineBaseComplex P hP r ⟶
      ((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex (.up ℕ)).obj
        (affineBaseComplex Q hQ r) :=
  (alternatingCofaceMapComplex (ModuleCat.{u} A)).map (affineBaseAnyRestrictedMap f hP hQ r) ≫
    ((alternatingCofaceFunctorIso (ModuleCat.restrictScalars f.toRingHom)).app
      (affineBaseModules Q hQ r)).inv

/-- 同じ元の余鎖射は、同じ元の剰余係数射のコホモロジー類を運ぶ。 -/
theorem affineAnyBaseRestrictedComplexMap_cohomology (i : ℕ)
    (z : hodgeTateCohomology' P hP r i) :
    homologyMap (affineAnyBaseRestrictedComplexMap f hP hQ r) i
        (affineNativeBaseCohomologyEquiv P hP r i z) =
      (((affineBaseComplex Q hQ r).sc i).mapHomologyIso
        (ModuleCat.restrictScalars f.toRingHom)).inv
        (affineNativeBaseCohomologyEquiv Q hQ r i
          (cohomologyMap _ _ (affineHTCoefficientReducedAny f hP hQ r) i z)) := by
  let U := ModuleCat.restrictScalars f.toRingHom
  let K := affineBaseComplex P hP r
  let L := affineBaseComplex Q hQ r
  let LU := (U.mapHomologicalComplex (.up ℕ)).obj L
  let a := affineAnyBaseRestrictedComplexMap f hP hQ r
  let q := affineHTCoefficientReducedAny f hP hQ r
  obtain ⟨c, rfl⟩ := cohomologyClass_surjective (reducedModel P hP r) i z
  let cP := moduleCycleRep A (reducedModel P hP r) (affineBaseCoefficients P hP r) i c
  let cQ := moduleCycleRep B (reducedModel Q hQ r) (affineBaseCoefficients Q hQ r) i
    (cocycleMap _ _ q i c)
  let v := ((L.sc i).mapCyclesIso U).inv cQ
  have hv : cyclesMap a i cP = v := by
    apply (ModuleCat.mono_iff_injective (LU.iCycles i)).mp inferInstance
    have h₁ := ConcreteCategory.congr_hom (cyclesMap_i a i) cP
    have h₂ := ConcreteCategory.congr_hom (coefficientCyclesIso_inv_inclusion (L.sc i) U) cQ
    change LU.iCycles i (cyclesMap a i cP) = a.f i (K.iCycles i cP) at h₁
    change LU.iCycles i v = L.iCycles i cQ at h₂
    rw [h₁, h₂, moduleCycleRep_apply, moduleCycleRep_apply]
    rfl
  have hp := ConcreteCategory.congr_hom (coefficientHomologyIso_inv_projection (L.sc i) U) cQ
  change ((L.sc i).mapHomologyIso U).inv (L.homologyπ i cQ) = LU.homologyπ i v at hp
  rw [affineNativeBaseCohomologyEquiv_class, cohomologyMap_class,
    affineNativeBaseCohomologyEquiv_class]
  change homologyMap a i (K.homologyπ i cP) = ((L.sc i).mapHomologyIso U).inv (L.homologyπ i cQ)
  rw [hp]
  have h := ConcreteCategory.congr_hom (homologyπ_naturality a i) cP
  change homologyMap a i (K.homologyπ i cP) = LU.homologyπ i (cyclesMap a i cP) at h
  exact h.trans (congrArg (LU.homologyπ i) hv)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
