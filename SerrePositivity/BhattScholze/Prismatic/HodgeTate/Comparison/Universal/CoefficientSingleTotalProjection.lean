module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CoefficientSingleTotalModel
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.MapExtendDegreeNormalization
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.BaseChangeTotalComponents
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CoefficientSingleTotalModel
import all SerrePositivity.HomologicalAlgebra.CochainProductTotalComponents
import all SerrePositivity.HomologicalAlgebra.ProductTotalSingleRow

/-!
# 元のsingle行のTot同型の指定成分

## 概要
元の離散行のTot同型は、同じ全次数の唯一の非零成分の射影である。

## 方針
零延長の指定同型と縦次数零のsingle行射影を展開する。

## 規約
新しい同型を選ばず、元のcoefficientSingleTotalIsoを計算する。

## 使われ方
HT04.R2の指定終域同型を通常係数の表示と照合する。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex AlgebraicTopology
open scoped Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded HomologicalAlgebra HTComparisonTotal HTUniversalCrystallineInput
open HomologicalAlgebra.CochainProductTotal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R]

/-- 元のTot同型の非負次数成分は、元の同じsingle行の指定射影。 -/
theorem coefficientSingleTotalIso_hom_f_nat
    (M : CosimplicialObject (ModuleCat.{u} R)) (n : ℕ) :
    (coefficientSingleTotalIso M).hom.f (n : ℤ) ≫
      (((alternatingCofaceMapComplex (ModuleCat.{u} R)).obj M).extendXIso
        ComplexShape.embeddingUpNat (i := n) rfl).hom =
    componentπ ((alternatingCofaceMapComplex (Complex R)).obj (coefficientSingleRows M)) n n ≫
      (singleObjXIsoOfEq (.up ℤ) 0 (M.obj ⦋n⦌) ((n : ℤ) - n) (by omega)).hom := by
  let S := HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0
  let K := (alternatingCofaceMapComplex (ModuleCat.{u} R)).obj M
  let W := (alternatingCofaceMapComplex (Complex R)).obj (coefficientSingleRows M)
  let V := (S.mapHomologicalComplex (.up ℕ)).obj K
  let α := (alternatingCofaceFunctorIso S).app M
  let β := SerrePositivity.mapExtendIso S K ComplexShape.embeddingUpNat
  let e := K.extendXIso ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl
  have hi : ∃ j : ℕ, ComplexShape.embeddingUpNat.f j = (n : ℤ) := ⟨n, rfl⟩
  have hchoose : hi.choose = n := by
    have hh : (hi.choose : ℤ) = (n : ℤ) := hi.choose_spec
    exact Int.ofNat.inj hh
  have hβn : β.inv.f (n : ℤ) = (rowIso V n).hom ≫ S.map e.inv := by
    change (SerrePositivity.mapExtendXIso S K ComplexShape.embeddingUpNat (n : ℤ)).inv = _
    simp only [SerrePositivity.mapExtendXIso, dite_eq_left hi, Iso.trans_inv,
      Functor.mapIso_inv, Iso.symm_inv, hchoose]
    dsimp only [rowIso, V, e]
    simp [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToHom_map]
  have hαn : α.inv.f n = 𝟙 _ := rfl
  have hαext : (extendMap α.inv ComplexShape.embeddingUpNat).f (n : ℤ) =
      (rowIso W n).hom ≫ (rowIso V n).inv := by
    rw [HomologicalComplex.extendMap_f α.inv ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl]
    change (rowIso W n).hom ≫ α.inv.f n ≫ (rowIso V n).inv = _
    erw [hαn, Category.id_comp]
  have hz : (rowIso V n).inv.f 0 ≫ (rowIso V n).hom.f 0 = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  have hnorm (b : ℤ) (hb : b = 0) :
      ProductTotal.π (W.extend ComplexShape.embeddingUpNat) n b n (by omega) ≫
        (rowIso W n).hom.f b ≫ (singleObjXIsoOfEq (.up ℤ) 0 (M.obj ⦋n⦌) b hb).hom =
      ProductTotal.π (W.extend ComplexShape.embeddingUpNat) n 0 n (by omega) ≫
        (rowIso W n).hom.f 0 ≫ (singleObjXSelf (.up ℤ) 0 (M.obj ⦋n⦌)).hom := by
    subst b
    rfl
  have hr : componentπ W n n ≫
      (singleObjXIsoOfEq (.up ℤ) 0 (M.obj ⦋n⦌) ((n : ℤ)-n) (by omega)).hom =
      ProductTotal.π (W.extend ComplexShape.embeddingUpNat) n 0 n (by omega) ≫
        (rowIso W n).hom.f 0 ≫ (singleObjXSelf (.up ℤ) 0 (M.obj ⦋n⦌)).hom :=
    hnorm ((n : ℤ)-n) (by omega)
  change _ = componentπ W n n ≫
    (singleObjXIsoOfEq (.up ℤ) 0 (M.obj ⦋n⦌) ((n : ℤ)-n) (by omega)).hom
  rw [hr]
  have hβ := ProductTotal.map_π β.inv (n : ℤ) 0 (n : ℤ) (by omega)
  have hα := ProductTotal.map_π (extendMap α.inv ComplexShape.embeddingUpNat)
    (n : ℤ) 0 (n : ℤ) (by omega)
  simp only [coefficientSingleTotalIso, Iso.trans_hom, Functor.mapIso_hom,
    HomologicalComplex.comp_f, Functor.comp_obj]
  change ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map α.inv).f (n : ℤ) ≫
    ((ProductTotal.functor (ModuleCat.{u} R)).map β.inv).f (n : ℤ) ≫
    (ProductTotal.singleRowIso (K.extend ComplexShape.embeddingUpNat)).hom.f (n : ℤ) ≫ e.hom = _
  change _ ≫ _ ≫ (ProductTotal.π _ (n : ℤ) 0 (n : ℤ) (by omega) ≫ _) ≫ _ = _
  simp only [Category.assoc]
  rw [reassoc_of% hβ]
  erw [reassoc_of% hα]
  rw [hαext, hβn]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [reassoc_of% hz]
  simp only [Category.id_comp, S, HomologicalComplex.single_map_f_self, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
