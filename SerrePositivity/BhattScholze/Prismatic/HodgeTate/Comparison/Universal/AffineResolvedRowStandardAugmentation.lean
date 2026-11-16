module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineDerivedCoefficientRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedRowBoundedSource
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedRowBoundedSource
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedCoefficientRows
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCoefficientSingleRows
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineCoverResolvedTotal

/-!
# 元のκの各項と元の指定被覆同型の一致

## 概要
元の半自由完備行射の各項は、独立に構成した始域比較と元の指定剰余被覆同型を計算する。

## 方針
元の完備化単位上で元の模型増大と係数増大を照合し、完備な終域への射の一意性を使う。

## 規約
κの擬同型性で射の等式を置き換えず、元のaffineReducedCoverTermIsoを保持する。

## 使われ方
HT04.R1の指定された項ごとの法則。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DifferentialGraded.ScalarExtension DerivedCompletion HTComparisonTotal
open HTComparisonResolution HTUniversalCrystallineInput
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 元の模型増大と元の加群比較は、同じ元の通常係数行射を保つ。 -/
theorem affineResolvedRow_standardAugmentation
    (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) (n : SimplexCategory) :
    let α := (Construction61.crystallineCoverMap P).toRingHom
    let M := (affineBaseModules P hP r).obj n
    let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
    let ε : (complexResolutionFunctor A).obj K ⟶ K := (complexResolutionAugmentation A).app K
    (affineResolvedRowUncompletedSourceIso P hP r n).hom ≫
      affineDerivedReducedCoefficientMap (Construction61.crystallineCoverMap P) hP
        (Construction61.crystallineCover_bounded P) r n =
    DerivedCategory.Q.map
      (((ModuleCat.extendScalars α).mapHomologicalComplex (.up ℤ)).map ε ≫
        (affineAnyExtendedSingleRowsMap (Construction61.crystallineCoverMap P) hP
          (Construction61.crystallineCover_bounded P) r).app n) := by
  let B : Type u := Construction61.crystallineCoverRing P
  let f := Construction61.crystallineCoverMap P
  let hQ := Construction61.crystallineCover_bounded P
  let α := f.toRingHom
  let M := (affineBaseModules P hP r).obj n
  let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
  let ε : (complexResolutionFunctor A).obj K ⟶ K := (complexResolutionAugmentation A).app K
  let t := nativeDerivedScalarModelIso α ε
    (complexResolutionAugmentation_quasiIso A K) (complexResolutionFunctor_kFlat A K)
  have hn := nativeDerivedScalarModelIso_comp_augmentation α ε
    (complexResolutionAugmentation_quasiIso A K) (complexResolutionFunctor_kFlat A K)
  have ht : t.inv ≫ (complexDerivedExtensionAugmentation α).app K =
      DerivedCategory.Q.map (((ModuleCat.extendScalars α).mapHomologicalComplex (.up ℤ)).map ε) := by
    rw [← hn, ← Category.assoc, t.inv_hom_id, Category.id_comp]
  have hb := unboundedBoundedModuleBaseChangeIso_augmentation α M
  simp only [affineResolvedRowUncompletedSourceIso, Iso.trans_hom, Iso.symm_hom,
    affineDerivedReducedCoefficientMap]
  simp only [Category.assoc]
  erw [reassoc_of% hb, reassoc_of% ht]
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ =
    DerivedCategory.Q.map (_ ≫ _ ≫ _)
  rw [Functor.map_comp, Functor.map_comp]
  rfl


end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
