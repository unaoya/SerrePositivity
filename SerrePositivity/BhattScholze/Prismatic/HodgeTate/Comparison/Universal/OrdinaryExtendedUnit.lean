module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.MapExtendDegreeNormalization
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.BaseChangeTotalComparison

/-!
# 通常係数拡大の単位と零延長

## 概要
元の非負余鎖射の随伴単位の正方形は、指定された零延長の同型を介して整数次数へ移る。

## 方針
非負次数では元の指定同型を通して各成分の単位の正方形へ戻し、負次数では始域の零性を使う。

## 規約
平坦性やホモロジー保存を仮定しない。

## 使われ方
元の被覆上の通常全複体同型の単位を、同じ剰余係数射へ照合する。
-/

public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open HTComparisonTotal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 元の成分ごとの単位の正方形は、零延長の元の指定比較へ移る。 -/
theorem ordinaryExtendedUnit (f : R →+* S)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (L : CochainComplex (ModuleCat.{u} S) ℕ)
    (g : ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℕ)).obj K ⟶ L)
    (h : K ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℕ)).obj L)
    (hu : ∀ n, (ModuleCat.extendRestrictScalarsAdj f).unit.app (K.X n) ≫
      (ModuleCat.restrictScalars f).map (g.f n) = h.f n) :
    complexBaseChangeUnit f (K.extend ComplexShape.embeddingUpNat) ≫
        ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map
          ((SerrePositivity.mapExtendIso (ModuleCat.extendScalars f) K
              ComplexShape.embeddingUpNat).hom ≫ extendMap g ComplexShape.embeddingUpNat) =
      extendMap h ComplexShape.embeddingUpNat ≫
        (SerrePositivity.mapExtendIso (ModuleCat.restrictScalars f) L
          ComplexShape.embeddingUpNat).inv := by
  let E := ModuleCat.extendScalars f
  let U := ModuleCat.restrictScalars f
  let e := ComplexShape.embeddingUpNat
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : 0 ≤ i
  · lift i to ℕ using hi
    apply (cancel_mono (U.map (L.extendXIso e (i := i) (i' := (i : ℤ)) rfl).hom)).mp
    change (ModuleCat.extendRestrictScalarsAdj f).unit.app ((K.extend e).X (i : ℤ)) ≫
        U.map ((SerrePositivity.mapExtendIso E K e).hom.f (i : ℤ) ≫ (extendMap g e).f (i : ℤ)) ≫
        U.map (L.extendXIso e (i := i) (i' := (i : ℤ)) rfl).hom =
      (extendMap h e).f (i : ℤ) ≫ (SerrePositivity.mapExtendIso U L e).inv.f (i : ℤ) ≫
        U.map (L.extendXIso e (i := i) (i' := (i : ℤ)) rfl).hom
    erw [mapExtendIso_inv_f_nat, extendMap_f h e (i := i) rfl]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    erw [← U.map_comp, Category.assoc, extendMap_f g e (i := i) rfl]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    erw [← Category.assoc, mapExtendIso_hom_f_nat, U.map_comp,
      ← Category.assoc, ← (ModuleCat.extendRestrictScalarsAdj f).unit.naturality]
    change (K.extendXIso e (i := i) (i' := (i : ℤ)) rfl).hom ≫
      ((ModuleCat.extendRestrictScalarsAdj f).unit.app (K.X i) ≫ U.map (g.f i)) = _
    erw [hu]
    simp [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, Category.assoc]
  · exact (K.isZero_extend_X e i (fun j hj => hi (hj ▸ Int.natCast_nonneg j))).eq_of_src _ _

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
