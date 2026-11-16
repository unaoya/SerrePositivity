module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedRowBoundedSource
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.FiniteCompletionComparisonUnit
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedRowBoundedSource
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CoverCompletionCoordinates
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteDerivedReflection

/-!
# 元の分解行の始域比較と元の二つの単位

## 概要
元の始域比較は、元の分解行の完備化単位を標準の上に有界な二つの単位へ送る。

## 方針
座標比較の単位の式、元の半自由模型の単位の式、標準単位の自然性を合成する。

## 規約
始域比較はκから独立に構成した元のものを使う。

## 使われ方
元のκの各項の射を元の指定被覆同型へ移す。
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

/-- κから独立な元の始域比較は、同じ元の二つの完備化単位を保つ。 -/
theorem affineResolvedRowBoundedSourceIso_unit
    (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ) (n : SimplexCategory) :
    let B : Type u := Construction61.crystallineCoverRing P
    let α := (Construction61.crystallineCoverMap P).toRingHom
    let M := (affineBaseModules P hP r).obj n
    let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
    let ε : (complexResolutionFunctor A).obj K ⟶ K := (complexResolutionAugmentation A).app K
    let Y := ((boundedAboveDerivedBaseChange α).obj (boundedAboveDerivedSingleFunctor.obj M)).obj
    DerivedCategory.Q.map (finiteCompletionUnit (coverImageCoordinates P)
        (baseChange α ((complexResolutionFunctor A).obj K))) ≫
      (affineResolvedRowBoundedSourceIso P hP r n).hom =
    (affineResolvedRowUncompletedSourceIso P hP r n).hom ≫
      (derivedComplexCompletionUnit B (p : B)).app Y ≫
      (derivedComplexCompletionUnit B (p : B)).app
        ((derivedComplexCompletionFunctor B (p : B)).obj Y) := by
  let B : Type u := Construction61.crystallineCoverRing P
  let α := (Construction61.crystallineCoverMap P).toRingHom
  let M := (affineBaseModules P hP r).obj n
  let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
  let ε : (complexResolutionFunctor A).obj K ⟶ K := (complexResolutionAugmentation A).app K
  let F := finiteDerivedCompletionFunctor (fun _ : Fin 2 => (p : B))
  let cpp := finiteDerivedCompletionComparison (fun _ : Fin 2 => (p : B))
  let L := baseChange α ((complexResolutionFunctor A).obj K)
  let t := affineResolvedRowUncompletedSourceIso P hP r n
  let Y := ((boundedAboveDerivedBaseChange α).obj (boundedAboveDerivedSingleFunctor.obj M)).obj
  have hc : DerivedCategory.Q.map (finiteCompletionUnit (coverImageCoordinates P) L) ≫
      (coverImageCompletionNatIso P).hom.app ((complexResolutionFunctor A).obj K) =
      DerivedCategory.Q.map (finiteCompletionUnit (fun _ : Fin 2 => (p : B)) L) := by
    exact associatedFiniteCompletionIso_unit (coverImageCoordinates P)
      (fun _ : Fin 2 => (p : B)) (coverImageCoordinates_associated P) L
  have hi : DerivedCategory.Q.map (finiteCompletionUnit (fun _ : Fin 2 => (p : B)) L) ≫
      cpp.inv.app L = (finiteDerivedCompletionUnit (fun _ : Fin 2 => (p : B))).app (DerivedCategory.Q.obj L) := by
    simpa only [Functor.mapIso_refl, Iso.refl_trans, Iso.refl_inv, Category.id_comp, Iso.app_inv]
      using finiteCompletionComparisonIso_unit (fun _ : Fin 2 => (p : B)) (Iso.refl (DerivedCategory.Q.obj L))
  have hn := (finiteDerivedCompletionUnit (fun _ : Fin 2 => (p : B))).naturality t.hom
  simp only [Functor.id_map] at hn
  simp only [affineResolvedRowBoundedSourceIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Iso.symm_hom]
  change DerivedCategory.Q.map (finiteCompletionUnit (coverImageCoordinates P) L) ≫
      (coverImageCompletionNatIso P).hom.app ((complexResolutionFunctor A).obj K) ≫
      cpp.inv.app L ≫ F.map t.hom = _
  calc
    _ = DerivedCategory.Q.map (finiteCompletionUnit (fun _ : Fin 2 => (p : B)) L) ≫
        cpp.inv.app L ≫ F.map t.hom := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ cpp.inv.app L ≫ F.map t.hom) hc
    _ = (finiteDerivedCompletionUnit (fun _ : Fin 2 => (p : B))).app (DerivedCategory.Q.obj L) ≫
        F.map t.hom := by
      simpa only [Category.assoc] using congrArg (fun k => k ≫ F.map t.hom) hi
    _ = t.hom ≫ (finiteDerivedCompletionUnit (fun _ : Fin 2 => (p : B))).app Y := hn.symm
    _ = _ := by
      simp only [finiteDerivedCompletionUnit, finiteDerivedCompletionFunctor,
        Functor.id_obj, Functor.comp_obj, Fin.init, NatTrans.id_app, Category.id_comp, Category.assoc] <;> rfl

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
