module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.DerivedScalarAnnihilation
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineReducedCoverTerms
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CoverCompletionCoordinates
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic

/-!
# 元の剰余行の被覆への導来底変換の完備性

## 概要
元の剰余行の生成元による零化から、被覆先での完備化前の導来底変換のp完備性を得る。

## 方針
元の商射の全射性で零化を示し、導来底変換のスカラー倍と像の生成元の同伴性を使う。

## 規約
係数環の平坦性を追加しない。完備化の標準単位による同型で元の項の比較へ接続する。

## 使われ方
標準行射の擬同型性を通常の係数拡大の標準増大へ照合する。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 元の剰余行は、元の基底環の選択生成元で零化される。 -/
theorem affineBaseModule_generator_zero (n : SimplexCategory) :
    P.generator • 𝟙 ((affineBaseModules P hP r).obj n) = 0 := by
  haveI := (affineFullBaseReduction_shortExact P hP r n).epi_g
  apply (cancel_epi ((affineFullBaseProjection P hP r).app n)).mp
  simpa only [Linear.smul_comp, Linear.comp_smul, Category.comp_id, Category.id_comp, comp_zero] using
    affineFullBaseProjection_zero P hP r n

/-- 零次数に置いた同じ元の剰余行も、元の選択生成元で零化される。 -/
theorem affineBaseSingle_generator_zero (n : SimplexCategory) :
    P.generator • 𝟙 (boundedAboveDerivedSingleFunctor.obj ((affineBaseModules P hP r).obj n)) = 0 := by
  apply (DerivedCategory.Minus.ι : DerivedCategory.Minus (ModuleCat.{u} A) ⥤
    DerivedCategory (ModuleCat.{u} A)).map_injective
  rw [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero]
  change P.generator • 𝟙 ((moduleObjectFunctor A).obj ((affineBaseModules P hP r).obj n)) = 0
  have h := congrArg (moduleObjectFunctor A).map (affineBaseModule_generator_zero P hP r n)
  simpa only [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero] using h

/-- 元の剰余行の被覆への実際の導来底変換は、完備化する前からp導来完備。 -/
theorem affineReducedCoverBaseChange_complete_p (n : SimplexCategory) :
    IsComplete (Construction61.crystallineCoverRing P) (p : Construction61.crystallineCoverRing P)
      ((boundedAboveDerivedBaseChange (Construction61.crystallineCoverMap P).toRingHom).obj
        (boundedAboveDerivedSingleFunctor.obj ((affineBaseModules P hP r).obj n))).obj := by
  have h := derivedBaseChange_complete_of_scalar_zero
    (Construction61.crystallineCoverMap P).toRingHom P.generator
    (boundedAboveDerivedSingleFunctor.obj ((affineBaseModules P hP r).obj n))
    (affineBaseSingle_generator_zero P hP r n)
  exact (isComplete_associated_iff _ _ (coverImageCoordinates_associated P 1) _).mp h

/-- 元の二座標完備化への標準単位は、元の剰余行の被覆への導来底変換上で同型。 -/
def affineReducedCoverBaseChangeCompletionIso (n : SimplexCategory) :
    ((boundedAboveDerivedBaseChange (Construction61.crystallineCoverMap P).toRingHom).obj
      (boundedAboveDerivedSingleFunctor.obj ((affineBaseModules P hP r).obj n))).obj ≅
    (pairCompletedBaseChange (Construction61.crystallineCoverMap P).toRingHom
      (p : Construction61.crystallineCoverRing P) (p : Construction61.crystallineCoverRing P)
      (boundedAboveDerivedSingleFunctor.obj ((affineBaseModules P hP r).obj n))).obj := by
  let B := Construction61.crystallineCoverRing P
  let Y := ((boundedAboveDerivedBaseChange (Construction61.crystallineCoverMap P).toRingHom).obj
    (boundedAboveDerivedSingleFunctor.obj ((affineBaseModules P hP r).obj n))).obj
  have hp := affineReducedCoverBaseChange_complete_p P hP r n
  exact derivedComplexCompletionUnitIso B (p : B) Y hp ≪≫
    derivedComplexCompletionUnitIso B (p : B)
      ((derivedComplexCompletionFunctor B (p : B)).obj Y)
      (derivedComplexCompletionFunctor_isComplete B (p : B) Y)

/-- 元の完備化前の導来底変換も、被覆上の元の剰余行の零次数対象と同型。 -/
def affineReducedCoverBaseChangeTermIso (n : SimplexCategory) :
    ((boundedAboveDerivedBaseChange (Construction61.crystallineCoverMap P).toRingHom).obj
      (boundedAboveDerivedSingleFunctor.obj ((affineBaseModules P hP r).obj n))).obj ≅
        (moduleObjectFunctor (Construction61.crystallineCoverRing P)).obj
          ((affineBaseModules (Construction61.crystallineCover P)
            (Construction61.crystallineCover_bounded P) r).obj n) :=
  affineReducedCoverBaseChangeCompletionIso P hP r n ≪≫ affineReducedCoverTermIso P hP r n

/-- 被覆への係数拡大では、元の剰余行との高次Torは消える。 -/
theorem affineReducedCover_scalarExtensionTorVanishing (n : SimplexCategory) :
    scalarExtensionTorVanishing (Construction61.crystallineCoverMap P).toRingHom
      ((affineBaseModules P hP r).obj n) := by
  intro i hi
  let α := (Construction61.crystallineCoverMap P).toRingHom
  let M := (affineBaseModules P hP r).obj n
  let N := (affineBaseModules (Construction61.crystallineCover P)
    (Construction61.crystallineCover_bounded P) r).obj n
  have hz : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat (Construction61.crystallineCoverRing P)) (-(i : ℤ))).obj
        ((boundedAboveDerivedBaseChange α).obj (boundedAboveDerivedSingleFunctor.obj M)).obj) :=
    (derivedSingleHomology_isZero N (-(i : ℤ)) (by omega)).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat (Construction61.crystallineCoverRing P))
        (-(i : ℤ))).mapIso (affineReducedCoverBaseChangeTermIso P hP r n))
  exact ((boundedAboveDerivedBaseChangeModuleTorIso α i).app M).isZero_iff.mp
    ((ModuleCat.restrictScalars α).map_isZero hz)

/-- 元の剰余行の被覆への導来底変換の標準増大は同型である。 -/
theorem affineReducedCover_derivedAugmentation_isIso (n : SimplexCategory) :
    IsIso ((boundedAboveDerivedBaseChangeModuleAugmentation
      (Construction61.crystallineCoverMap P).toRingHom).app ((affineBaseModules P hP r).obj n)) := by
  let α := (Construction61.crystallineCoverMap P).toRingHom
  let M := (affineBaseModules P hP r).obj n
  haveI := (derivedModuleBaseChangeAugmentation_isIso_iff α M).mpr
    (affineReducedCover_scalarExtensionTorVanishing P hP r n)
  change IsIso ((boundedAboveDerivedBaseChangeModuleNatIso α).hom.app M ≫
    (derivedModuleBaseChangeAugmentation α).app M)
  infer_instance

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
