module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.BaseChangeHomologyUnit
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.HomologyIsoComposition

/-!
# 微分零の元の模型での通常係数拡大のホモロジー

## 概要
元の随伴単位によるホモロジーの係数拡大の射は、出る微分が零の次数では同型。

## 方針
係数拡大の余核の保存で短複体のホモロジー同型を作り、同じ元の単位と照合する。

## 規約
任意の複体へのホモロジーの保存を仮定しない。元の指定された比較射を使う。

## 使われ方
元の二次数の形式模型で、元のηのH₀/H₁を通常係数拡大へ移す。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded HTComparisonTotal HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 出る微分が零なら、元のホモロジー単位の転置は同型。 -/
theorem complexBaseChangeHomologyComparison_isIso_of_zero_g (f : R →+* S)
    (K : Complex R) (i : ℤ) (hg : (K.sc i).g = 0) :
    IsIso (complexBaseChangeHomologyComparison f K i) := by
  let E := ModuleCat.extendScalars f
  let U := ModuleCat.restrictScalars f
  let X := K.sc i
  haveI : E.PreservesLeftHomologyOf X := E.preservesLeftHomology_of_zero_g X hg
  haveI : E.PreservesRightHomologyOf X := E.preservesRightHomology_of_zero_g X hg
  haveI : (E ⋙ U).PreservesLeftHomologyOf X := (E ⋙ U).preservesLeftHomology_of_zero_g X hg
  haveI : (E ⋙ U).PreservesRightHomologyOf X := (E ⋙ U).preservesRightHomology_of_zero_g X hg
  let e := X.mapHomologyIso E
  let eU := (X.map E).mapHomologyIso U
  let eI := X.mapHomologyIso (𝟭 (ModuleCat.{u} R))
  have hc := coefficientHomologyIso_comp_hom X E U
  have hu : complexBaseChangeHomologyUnit f K i ≫ U.map e.hom =
      eI.hom ≫ (ModuleCat.extendRestrictScalarsAdj f).unit.app (K.homology i) := by
    change ShortComplex.homologyMap
      (X.mapNatTrans (ModuleCat.extendRestrictScalarsAdj f).unit) ≫
        ((X.map E).mapHomologyIso U).hom ≫ U.map (X.mapHomologyIso E).hom = _
    rw [← hc]
    rw [ShortComplex.homologyMap_mapNatTrans]
    change eI.hom ≫ (ModuleCat.extendRestrictScalarsAdj f).unit.app X.homology ≫
      (X.mapHomologyIso (E ⋙ U)).inv ≫ (X.mapHomologyIso (E ⋙ U)).hom = _
    rw [Iso.inv_hom_id, Category.comp_id]
    rfl
  have he : complexBaseChangeHomologyComparison f K i ≫ e.hom = E.map eI.hom := by
    apply ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right]
    simp only [complexBaseChangeHomologyComparison, Equiv.apply_symm_apply]
    have hr := (ModuleCat.extendRestrictScalarsAdj f).homEquiv_naturality_left eI.hom (𝟙 _)
    simp only [Category.comp_id, Adjunction.homEquiv_id] at hr
    exact hu.trans hr.symm
  haveI : IsIso (complexBaseChangeHomologyComparison f K i ≫ e.hom) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ e.hom

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
