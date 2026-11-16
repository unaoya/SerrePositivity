module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CompletedRawCompatibility

/-!
# 標準 S 完備比較の制限と元の単位

## 概要
標準 S 線形比較を既存の導来係数制限で写し、指定した R 積 Tot へ渡す。

## 方針
係数制限の分解自然同型と標準 S 単位による正規化を、そのまま使う。

## 規約
S 線形の比較射自体は既存の標準単位による一意な延長である。

## 使われ方
BS 著者版 Lemma 4.22 の元の標準比較を保った同型性の判定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
open SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 具体的な源と標的を保った、既存の導来係数制限の射。 -/
def derivedComplexRestrictionMap (f : R →+* S) {K M : Complex S}
    (h : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj M) :
    DerivedCategory.Q.obj (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj M) :=
  (derivedRestrictScalarsFactors f).inv.app K ≫ (derivedRestrictScalars f).map h ≫
    (derivedRestrictScalarsFactors f).hom.app M

/-- 複体の実際の射は、元の複体の係数制限の射に一致する。 -/
@[simp] theorem derivedComplexRestrictionMap_Q (f : R →+* S) {K M : Complex S} (g : K ⟶ M) :
    derivedComplexRestrictionMap f (DerivedCategory.Q.map g) =
      DerivedCategory.Q.map (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map g) := by
  have hn := (derivedRestrictScalarsFactors f).hom.naturality g
  simp only [Functor.comp_map] at hn
  dsimp only [derivedComplexRestrictionMap]
  rw [hn]
  simp only [← Category.assoc, ← Iso.app_inv, ← Iso.app_hom, Iso.inv_hom_id, Category.id_comp]

/-- 実際の複体の射との前合成も、そのまま制限される。 -/
@[reassoc] theorem derivedComplexRestrictionMap_precomp (f : R →+* S)
    {K M N : Complex S} (g : K ⟶ M) (h : DerivedCategory.Q.obj M ⟶ DerivedCategory.Q.obj N) :
    DerivedCategory.Q.map (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map g) ≫
        derivedComplexRestrictionMap f h =
      derivedComplexRestrictionMap f (DerivedCategory.Q.map g ≫ h) := by
  have hn := (derivedRestrictScalarsFactors f).inv.naturality g
  simp only [Functor.comp_map] at hn
  dsimp only [derivedComplexRestrictionMap]
  rw [← Category.assoc, hn, Functor.map_comp]
  simp only [Category.assoc]

/-- 同じ標準 S 比較を制限し、同じ指定 R 積 Tot へ移す。 -/
def restrictedStandardCompletedComparison (f : R →+* S) {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) {P : Complex R} (q : P ⟶ total K) :
    DerivedCategory.Q.obj (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
      ((finiteCompletionFunctor (fun j => f (x j))).obj (baseChange f P))) ⟶
      DerivedCategory.Q.obj (total (restrictedCompletedBaseChangeRows f x K)) :=
  derivedComplexRestrictionMap f (finiteCompletedBaseChangeModelComparison f x K q) ≫
    DerivedCategory.Q.map (restrictionTotalIso f (standardCompletedBaseChangeRows f x K)).hom

namespace ScalarResolution
variable {f : R →+* S} (L : ScalarResolution f)

/-- 元の係数増大と S 単位による正規化は、元の R 水平射の Tot である。 -/
@[reassoc] theorem source_comp_restrictedStandardCompletedComparison {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) {P : Complex R} (q : P ⟶ total K) :
    DerivedCategory.Q.map (L.toRestrictedCompletedSource x P) ≫
      restrictedStandardCompletedComparison f x K q =
    DerivedCategory.Q.map (L.tensorFunctor.map q ≫ tensorTotalComparison L.complex K ≫
      (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map (L.toRestrictedCompletedRows x K)) := by
  dsimp only [toRestrictedCompletedSource, restrictedStandardCompletedComparison]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [derivedComplexRestrictionMap_precomp_assoc,
    unit_comp_finiteCompletedBaseChangeModelComparison, derivedComplexRestrictionMap_Q]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg DerivedCategory.Q.map (L.rawCompletedComparison_compatibility x K q)

end ScalarResolution
end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
