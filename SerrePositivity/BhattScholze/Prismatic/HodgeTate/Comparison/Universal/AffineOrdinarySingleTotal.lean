module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineAnySingleRowUnit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.SingleRowsOrdinaryTotal
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOrientedOrdinaryRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineOriginalTotalModel

/-!
# 元のsingle行からの通常Tot比較と同じ係数射

## 概要
元の随伴単位からの通常Tot比較を使い、元の係数射に戻る単位の正方形を固定する。

## 方針
係数制限のTot自然同型の逆の自然性で各行へ戻し、元のsingle行の単位の式を使う。

## 規約
元の指定射を使う。始域の生成元をpにはしない。

## 使われ方
元のηの通常係数拡大を、被覆上の元の標準HT写像へ照合する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DerivedCompletion HomologicalAlgebra HTComparisonTotal HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (r : ℕ)

/-- 元の通常係数行射を元の通常Tot比較の後で読む、同じ複体の射。 -/
def affineAnySingleRowsOrdinaryTotalMap :
    baseChange f.toRingHom (cosimplicialTotal (affineBaseSingleRows P hP r)) ⟶
      cosimplicialTotal (affineBaseSingleRows Q hQ r) :=
  baseChangeTotalComparison f.toRingHom
      ((alternatingCofaceMapComplex (Complex A)).obj (affineBaseSingleRows P hP r)) ≫
    (cochainProductTotalizationFunctor (ModuleCat.{u} B)).map
      (((alternatingCofaceFunctorIso
          ((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ))).app
        (affineBaseSingleRows P hP r)).hom ≫
      (alternatingCofaceMapComplex (Complex B)).map (affineAnyExtendedSingleRowsMap f hP hQ r))

/-- 元の制限係数行射を、同じ元のTotの係数制限へ戻した複体の射。 -/
def affineAnySingleRowsRestrictedTotalMap :
    cosimplicialTotal (affineBaseSingleRows P hP r) ⟶
      ((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex (.up ℤ)).obj
        (cosimplicialTotal (affineBaseSingleRows Q hQ r)) :=
  (cochainProductTotalizationFunctor (ModuleCat.{u} A)).map
      ((alternatingCofaceMapComplex (Complex A)).map (affineAnyRestrictedSingleRowsMap f hP hQ r) ≫
      ((alternatingCofaceFunctorIso
        ((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex (.up ℤ))).app
          (affineBaseSingleRows Q hQ r)).inv) ≫
    (restrictionTotalIso f.toRingHom
      ((alternatingCofaceMapComplex (Complex B)).obj (affineBaseSingleRows Q hQ r))).inv

/-- 元の通常Tot射と元の係数行射は、元の随伴単位の正方形を持つ。 -/
@[reassoc] theorem affineAnySingleRowsOrdinaryTotalMap_unit :
    complexBaseChangeUnit f.toRingHom (cosimplicialTotal (affineBaseSingleRows P hP r)) ≫
      ((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex (.up ℤ)).map
        (affineAnySingleRowsOrdinaryTotalMap f hP hQ r) =
      affineAnySingleRowsRestrictedTotalMap f hP hQ r := by
  let X := affineBaseSingleRows P hP r
  let Y := affineBaseSingleRows Q hQ r
  let E := (ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)
  let U := (ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex (.up ℤ)
  let K := (alternatingCofaceMapComplex (Complex A)).obj X
  let L := (alternatingCofaceMapComplex (Complex B)).obj Y
  let g := ((alternatingCofaceFunctorIso E).app X).hom ≫
    (alternatingCofaceMapComplex (Complex B)).map (affineAnyExtendedSingleRowsMap f hP hQ r)
  let h := (alternatingCofaceMapComplex (Complex A)).map (affineAnyRestrictedSingleRowsMap f hP hQ r) ≫
    ((alternatingCofaceFunctorIso U).app Y).inv
  have hh : rowsBaseChangeUnit f.toRingHom K ≫
      (U.mapHomologicalComplex (.up ℕ)).map g = h := by
    apply HomologicalComplex.Hom.ext
    funext n
    change complexBaseChangeUnit f.toRingHom (X.obj (SimplexCategory.mk n)) ≫
      U.map ((((alternatingCofaceFunctorIso E).app X).hom.f n) ≫
        (affineAnyExtendedSingleRowsMap f hP hQ r).app (SimplexCategory.mk n)) =
      (affineAnyRestrictedSingleRowsMap f hP hQ r).app (SimplexCategory.mk n) ≫
        (((alternatingCofaceFunctorIso U).app Y).inv.f n)
    erw [show ((alternatingCofaceFunctorIso E).app X).hom.f n = 𝟙 _ from rfl,
      show ((alternatingCofaceFunctorIso U).app Y).inv.f n = 𝟙 _ from rfl,
      Category.id_comp, Category.comp_id]
    exact affineAnyExtendedSingleRowsMap_unit f hP hQ r (SimplexCategory.mk n)

  have hn := (restrictionTotalNatIso f.toRingHom).inv.naturality g
  change (cochainProductTotalizationFunctor (ModuleCat.{u} A)).map
      ((U.mapHomologicalComplex (.up ℕ)).map g) ≫ (restrictionTotalIso f.toRingHom L).inv =
    (restrictionTotalIso f.toRingHom ((baseChangeRowsFunctor f.toRingHom).obj K)).inv ≫
      U.map ((cochainProductTotalizationFunctor (ModuleCat.{u} B)).map g) at hn
  change complexBaseChangeUnit f.toRingHom (total K) ≫
      U.map (baseChangeTotalComparison f.toRingHom K ≫
        (cochainProductTotalizationFunctor (ModuleCat.{u} B)).map g) =
    (cochainProductTotalizationFunctor (ModuleCat.{u} A)).map h ≫ _
  rw [Functor.map_comp, ← Category.assoc, complexBaseChangeUnit_comp_totalComparison]
  change (cochainProductTotalizationFunctor (ModuleCat.{u} A)).map (rowsBaseChangeUnit f.toRingHom K) ≫
    (restrictionTotalIso f.toRingHom _).inv ≫
      U.map ((cochainProductTotalizationFunctor (ModuleCat.{u} B)).map g) = _
  rw [← hn, ← Category.assoc, ← Functor.map_comp, hh]

variable (hg : Q.generator = (p : B))
include hg

/-- 元の通常Tot射は、終域の生成元がpのとき同型。 -/
theorem affineAnySingleRowsOrdinaryTotalMap_isIso :
    IsIso (affineAnySingleRowsOrdinaryTotalMap f hP hQ r) := by
  haveI : IsIso (baseChangeTotalComparison f.toRingHom
      ((alternatingCofaceMapComplex (Complex A)).obj (affineBaseSingleRows P hP r))) := by
    apply baseChangeTotalComparison_isIso_of_singleRows
    intro n j hj
    change IsZero (((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
      ((affineBaseModules P hP r).obj (SimplexCategory.mk n))).X j)
    exact isZero_single_obj_X (.up ℤ) 0 _ j hj
  haveI (n : SimplexCategory) : IsIso ((affineAnyExtendedSingleRowsMap f hP hQ r).app n) :=
    affineAnyExtendedSingleRowsMap_app_isIso f hP hQ hg r n
  haveI : IsIso (affineAnyExtendedSingleRowsMap f hP hQ r) :=
    NatIso.isIso_of_isIso_app _
  dsimp only [affineAnySingleRowsOrdinaryTotalMap]
  infer_instance

/-- 同じ標準Tot射で指定する、元のHT全複体の通常係数拡大の同型。 -/
def affineAnyOrdinaryTotalViaRowsIso :
    baseChange f.toRingHom (affineComplexOnBase P r (affineHTTotalComplex P hP r)) ≅
      affineComplexOnBase Q r (affineHTTotalComplex Q hQ r) := by
  haveI := affineAnySingleRowsOrdinaryTotalMap_isIso f hP hQ r hg
  exact ((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)).mapIso
      (affineBaseSingleTotalPolynomialIso P hP r).symm ≪≫
    asIso (affineAnySingleRowsOrdinaryTotalMap f hP hQ r) ≪≫
    affineBaseSingleTotalPolynomialIso Q hQ r

/-- 元の全複体での指定同型も、同じ元の係数行射の単位の正方形を持つ。 -/
@[reassoc] theorem affineAnyOrdinaryTotalViaRowsIso_unit :
    complexBaseChangeUnit f.toRingHom (affineComplexOnBase P r (affineHTTotalComplex P hP r)) ≫
      ((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex (.up ℤ)).map
        (affineAnyOrdinaryTotalViaRowsIso f hP hQ r hg).hom =
      (affineBaseSingleTotalPolynomialIso P hP r).inv ≫
        affineAnySingleRowsRestrictedTotalMap f hP hQ r ≫
          ((ModuleCat.restrictScalars f.toRingHom).mapHomologicalComplex (.up ℤ)).map
            (affineBaseSingleTotalPolynomialIso Q hQ r).hom := by
  simp only [affineAnyOrdinaryTotalViaRowsIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc, ← complexBaseChangeUnit_naturality, Category.assoc,
    affineAnySingleRowsOrdinaryTotalMap_unit_assoc]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
