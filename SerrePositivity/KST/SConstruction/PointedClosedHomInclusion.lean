module
public import SerrePositivity.KST.SConstruction.LaxClosedFamilyMap
public import SerrePositivity.KST.Spectra.PointedEnrichment
public import SerrePositivity.KST.Spectra.PointedVertexComparison

/-! # 標準の点つき豊穣から元の閉内部 Hom への包含
概要：標準 basedHom の包含は、全射・恒等・全合成を同じ閉内部 Hom で回収する。
方針：点つき忘却の lax monoidal 比較を、元の smash curry の包含式と同定する。
規約：標準の点つき豊穣を変更しない。使われ方：元の商上の全族の点つき豊穣包装。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open Spectra

/-- 点つき忘却の全閉 Hom 比較は、元の同じ basedHom の包含そのもの。 -/
lemma pointedLaxClosedFamilyMap_eq (X Y : PointedSimplicialSet.{u}) :
    laxClosedFamilyMap PointedSimplicialSet.forget X Y = PointedObject.basedHomι X Y := by
  have h := PointedObject.smashCurry_ι ((ihom.ev X).app Y)
  have hc : curry ((ihom.ev X).app Y) = 𝟙 ((ihom X).obj Y) := by
    rw [← uncurry_id_eq_ev, curry_uncurry]
  erw [← PointedMapping.curry_eq_smashCurry, hc,
    Under.id_right, Category.id_comp] at h
  exact h.symm

local instance pointedClosedInclusion_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の通常の点つき射の単位からの表示は、包含後に同じ基礎射を回収する。 -/
lemma pointedClosedHomInclusion_hom {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    eHomEquiv SSet.{u} f ≫ PointedObject.basedHomι X Y = curry' f.right := by
  change PointedSimplicialSet.unitUnderlyingHom (PointedObject.basedHom X Y) (curry' f) ≫
    PointedObject.basedHomι X Y = _
  erw [← PointedSimplicialSet.forgetUnit_comp]
  exact (congrArg (fun q => (PointedSimplicialSet.forgetUnit ≫ (curry' f).right) ≫ q)
    (pointedLaxClosedFamilyMap_eq X Y)).symm.trans
      (laxClosedFamilyMap_hom PointedSimplicialSet.forget f)

/-- 標準の点つき豊穣恒等射は、元の閉内部 Hom の恒等射へ包含される。 -/
lemma pointedClosedHomInclusion_id (X : PointedSimplicialSet.{u}) :
    eId SSet.{u} X ≫ PointedObject.basedHomι X X = MonoidalClosed.id X.right := by
  simpa only [eHomEquiv_id, Under.id_right, curry'_id] using
    pointedClosedHomInclusion_hom (𝟙 X)

/-- 標準の点つき豊穣合成は、元の全閉内部 Hom の合成へ包含される。 -/
lemma pointedClosedHomInclusion_comp (X Y Z : PointedSimplicialSet.{u}) :
    eComp SSet.{u} X Y Z ≫ PointedObject.basedHomι X Z =
      (PointedObject.basedHomι X Y ⊗ₘ PointedObject.basedHomι Y Z) ≫
        MonoidalClosed.comp X.right Y.right Z.right := by
  have h := laxClosedFamilyMap_comp PointedSimplicialSet.forget X Y Z
  rw [pointedLaxClosedFamilyMap_eq, pointedLaxClosedFamilyMap_eq,
    pointedLaxClosedFamilyMap_eq] at h
  exact h

end SerrePositivity.KST.SConstruction
