module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CoefficientSingleTotalBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CoefficientSingleTotalNaturality
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineNativeOrdinaryCoefficientUnit
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineNativeOrdinaryCoefficientUnit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrdinaryTarget
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineResolvedCoefficientRows
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrdinaryTarget

/-!
# 元の通常Tot係数射と元のHT全複体の係数同型

## 概要
同じ元の係数射を、元のsingle行と元のHT全複体の二つの表示で照合する。

## 方針
元のsingle行Tot同型の係数変更と自然性を使う。

## 規約
元の通常係数同型も指定Tot同型も再定義しない。

## 使われ方
HT04.R2の指定e_targetを通常係数表示と同定する。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex AlgebraicTopology
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded HomologicalAlgebra HTComparisonTotal HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}

/-- 元の通常Tot係数射は、元のHT全複体の同じ通常係数同型を計算する。 -/
theorem affineOrdinaryCofaceCoefficient_compatibility
    (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
    (hg : Q.generator = (p : B)) (r : ℕ) :
    let E := (ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)
    E.map (affineBaseSingleTotalPolynomialIso P hP r).inv ≫
      affineOrdinaryCofaceCoefficient f hP hQ r ≫ (affineBaseSingleTotalPolynomialIso Q hQ r).hom =
      (affineAnyOrdinaryTotalIso f hP hQ hg r).hom := by
  let E := (ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)
  let M := affineBaseModules P hP r
  let N := affineBaseModules Q hQ r
  let T := alternatingCofaceMapComplex (Complex B) ⋙ cochainProductTotalizationFunctor (ModuleCat.{u} B)
  let c := affineBaseAnyOrdinaryCoefficientMap f hP hQ r
  let eP := affineBaseSingleTotalPolynomialIso P hP r
  let eQ := affineBaseSingleTotalPolynomialIso Q hQ r
  let m := SerrePositivity.mapExtendIso (ModuleCat.extendScalars f.toRingHom)
    (affineBaseComplex P hP r) ComplexShape.embeddingUpNat
  have hrows : (affineAnyOrdinaryRowsIso f hP hQ hg r).hom = c := by
    apply NatTrans.ext
    funext n
    rfl
  have hb : affineOrdinaryCofaceCoefficient f hP hQ r ≫ (coefficientSingleTotalIso N).hom =
      E.map (coefficientSingleTotalIso M).hom ≫ m.hom ≫
      extendMap (affineAnyOrdinaryComplexIso f hP hQ hg r).hom
        ComplexShape.embeddingUpNat := by
    have hbase := coefficientSingleTotalIso_baseChange f.toRingHom M
    have hnat := coefficientSingleTotalIso_naturality c
    have hbase' := congrArg (fun k => k ≫
      extendMap ((alternatingCofaceMapComplex (ModuleCat.{u} B)).map c) ComplexShape.embeddingUpNat) hbase
    simp only [Category.assoc] at hbase'
    simp only [Functor.comp_map] at hnat
    simp only [affineOrdinaryCofaceCoefficient, affineAnyExtendedSingleRowsMap,
      Functor.map_comp, Functor.comp_map, Category.assoc]
    rw [hnat]
    simpa only [m, E, M, N, affineBaseComplex, affineAnyOrdinaryComplexIso, Iso.trans_hom,
      hrows, c,
      Functor.mapIso_hom, HomologicalComplex.extendMap_comp, Functor.comp_map, Category.assoc]
      using hbase'.symm
  apply (cancel_mono (affineOriginalBaseComplexIso Q hQ r).hom).mp
  calc
    _ = E.map eP.inv ≫ affineOrdinaryCofaceCoefficient f hP hQ r ≫
        (coefficientSingleTotalIso N).hom := by
      simp only [E, eP, eQ, N, affineOriginalBaseComplexIso, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
    _ = E.map eP.inv ≫ E.map (coefficientSingleTotalIso M).hom ≫ m.hom ≫
        extendMap (affineAnyOrdinaryComplexIso f hP hQ hg r).hom
          ComplexShape.embeddingUpNat := by simpa only [Category.assoc] using congrArg (fun k => E.map eP.inv ≫ k) hb
    _ = _ := by
      simp only [E, eP, eQ, M, N, m, affineAnyOrdinaryTotalIso, affineOriginalBaseComplexIso,
        Iso.trans_inv, Iso.symm_inv, ComplexShape.Embedding.extendFunctor_map,
        Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
        Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
