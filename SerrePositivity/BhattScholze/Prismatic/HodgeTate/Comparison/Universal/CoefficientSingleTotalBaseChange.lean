module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CoefficientSingleTotalProjection
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCoefficientSingleRows

/-!
# 元のsingle行のTot同型と通常係数拡大

## 概要
元の指定Tot同型は、元の通常係数拡大の標準Tot比較を保つ。

## 方針
非負次数では唯一の非零行の指定射影で照合し、負次数では零性を使う。

## 規約
係数拡大の完全性は仮定しない。

## 使われ方
HT04.R2の指定終域同型の通常係数表示。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded HomologicalAlgebra HTComparisonTotal HTUniversalCrystallineInput
open HomologicalAlgebra.CochainProductTotal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A B : Type u} [CommRing A] [CommRing B]

/-- 元の指定single行Tot同型は元の通常係数拡大と可換。 -/
theorem coefficientSingleTotalIso_baseChange (f : A →+* B)
    (M : CosimplicialObject (ModuleCat.{u} A)) :
    let E := ModuleCat.extendScalars f
    let EC := E.mapHomologicalComplex (.up ℤ)
    EC.map (coefficientSingleTotalIso M).hom ≫
      (SerrePositivity.mapExtendIso E ((alternatingCofaceMapComplex (ModuleCat.{u} A)).obj M)
        ComplexShape.embeddingUpNat).hom ≫
      extendMap ((alternatingCofaceFunctorIso E).app M).hom ComplexShape.embeddingUpNat =
    baseChangeTotalComparison f ((alternatingCofaceMapComplex (Complex A)).obj (coefficientSingleRows M)) ≫
      (cochainProductTotalizationFunctor (ModuleCat.{u} B)).map
        ((alternatingCofaceFunctorIso EC).app (coefficientSingleRows M)).hom ≫
      (alternatingCofaceMapComplex (Complex B) ⋙ cochainProductTotalizationFunctor (ModuleCat.{u} B)).map
        (coefficientExtendedSingleRowsIso f M).hom ≫
      (coefficientSingleTotalIso (M ⋙ E)).hom := by

  let E := ModuleCat.extendScalars f
  let EC := E.mapHomologicalComplex (.up ℤ)
  let K := (alternatingCofaceMapComplex (ModuleCat.{u} A)).obj M
  let X := coefficientSingleRows M
  let L := (alternatingCofaceMapComplex (ModuleCat.{u} B)).obj (M ⋙ E)
  let T := cochainProductTotalizationFunctor (ModuleCat.{u} B)
  let AS := alternatingCofaceMapComplex (Complex B)
  let a := EC.map (coefficientSingleTotalIso M).hom ≫
    (SerrePositivity.mapExtendIso E K ComplexShape.embeddingUpNat).hom ≫
    extendMap ((alternatingCofaceFunctorIso E).app M).hom ComplexShape.embeddingUpNat
  let b := baseChangeTotalComparison f ((alternatingCofaceMapComplex (Complex A)).obj X) ≫
    T.map ((alternatingCofaceFunctorIso EC).app X).hom ≫
    T.map (AS.map (coefficientExtendedSingleRowsIso f M).hom) ≫
    (coefficientSingleTotalIso (M ⋙ E)).hom
  have hE (n : ℕ) : ((alternatingCofaceFunctorIso E).app M).hom.f n = 𝟙 _ := rfl
  have hEC (n : ℕ) : ((alternatingCofaceFunctorIso EC).app X).hom.f n = 𝟙 _ := rfl
  have hsingle (n : ℕ) (j : ℤ) (hj : j = 0) :
      ((coefficientExtendedSingleRowsIso f M).hom.app ⦋n⦌).f j ≫
        (singleObjXIsoOfEq (.up ℤ) 0 (E.obj (M.obj ⦋n⦌)) j hj).hom =
      E.map (singleObjXIsoOfEq (.up ℤ) 0 (M.obj ⦋n⦌) j hj).hom := by
    subst j
    change ((singleMapHomologicalComplex E (.up ℤ) 0).hom.app (M.obj ⦋n⦌)).f 0 ≫
      (singleObjXSelf (.up ℤ) 0 (E.obj (M.obj ⦋n⦌))).hom =
      E.map (singleObjXSelf (.up ℤ) 0 (M.obj ⦋n⦌)).hom
    rw [singleMapHomologicalComplex_hom_app_self]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hleft (n : ℕ) : a.f (n : ℤ) ≫
      (L.extendXIso ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl).hom =
      E.map (componentπ ((alternatingCofaceMapComplex (Complex A)).obj X) n n ≫
        (singleObjXIsoOfEq (.up ℤ) 0 (M.obj ⦋n⦌) ((n : ℤ)-n) (by omega)).hom) := by
    dsimp only [a, EC]
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, Category.assoc]
    erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    erw [hE n, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
    erw [mapExtendIso_hom_f_nat E K n]
    rw [← Functor.map_comp, coefficientSingleTotalIso_hom_f_nat]
  have hright (n : ℕ) : b.f (n : ℤ) ≫
      (L.extendXIso ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl).hom =
      E.map (componentπ ((alternatingCofaceMapComplex (Complex A)).obj X) n n ≫
        (singleObjXIsoOfEq (.up ℤ) 0 (M.obj ⦋n⦌) ((n : ℤ)-n) (by omega)).hom) := by
    dsimp only [b]
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [coefficientSingleTotalIso_hom_f_nat]
    erw [reassoc_of% (componentπ_naturality (AS.map (coefficientExtendedSingleRowsIso f M).hom) n n)]
    erw [reassoc_of% (componentπ_naturality ((alternatingCofaceFunctorIso EC).app X).hom n n)]
    erw [hEC n]
    simp only [HomologicalComplex.id_f, Category.id_comp]
    dsimp only [EC, E, X]
    erw [baseChangeTotalComparison_component_assoc]
    change E.map (componentπ ((alternatingCofaceMapComplex (Complex A)).obj X) n n) ≫
      ((coefficientExtendedSingleRowsIso f M).hom.app ⦋n⦌).f ((n : ℤ)-n) ≫
      (singleObjXIsoOfEq (.up ℤ) 0 (E.obj (M.obj ⦋n⦌)) ((n : ℤ)-n) (by omega)).hom = _
    rw [hsingle n _ (by omega), Functor.map_comp]
  change a = b
  apply HomologicalComplex.Hom.ext
  funext q
  by_cases hq : 0 ≤ q
  · lift q to ℕ using hq
    apply (cancel_mono (L.extendXIso ComplexShape.embeddingUpNat (i := q) (i' := (q : ℤ)) rfl).hom).mp
    exact (hleft q).trans (hright q).symm
  · have hz := L.isZero_extend_X ComplexShape.embeddingUpNat q (fun n hn => by
      change (n : ℤ) = q at hn; omega)
    exact hz.eq_of_tgt _ _

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
