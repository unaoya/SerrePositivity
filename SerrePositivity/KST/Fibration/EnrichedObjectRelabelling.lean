module
public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
public import SerrePositivity.KST.SConstruction.SSetInternalObject

/-!
概要：対象の座標の等号に沿い、元の全 Hom を保つ豊穣関手の読み替え。
方針：対象関数の等号を消去し、元の Hom 作用と評価射を回収する。
規約：全パラメータ単体を保ち、対象の表示だけを輸送する。
使われ方：core S 実現の零化円柱を元の対象座標へ戻す。
-/

@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Fibration
section Enriched
variable {C : Type v} {D : Type w} [EnrichedCategory SSet.{u} C]
  [EnrichedCategory SSet.{u} D]

/-- 対象関数の等号で全 Hom の型だけを読み替え、元の豊穣関手を保持する。 -/
def relabelEnrichedObjects (F : EnrichedFunctor SSet.{u} C D) (obj : C → D)
    (h : F.obj = obj) : EnrichedFunctor SSet.{u} C D where
  obj := obj
  map X Y := F.map X Y ≫ eqToHom (congrArg (fun k : C → D => k X ⟶[SSet.{u}] k Y) h)
  map_id X := by
    cases h
    simpa only [eqToHom_refl, Category.comp_id] using F.map_id X
  map_comp X Y Z := by
    cases h
    simpa only [eqToHom_refl, Category.comp_id] using F.map_comp X Y Z

/-- 座標の等号による読み替えは、全単体を含む元の豊穣関手そのものに等しい。 -/
theorem relabelEnrichedObjects_eq (F : EnrichedFunctor SSet.{u} C D) (obj : C → D)
    (h : F.obj = obj) : relabelEnrichedObjects F obj h = F := by
  cases h
  apply EnrichedFunctor.ext SSet
  case h_obj => intro X; rfl
  case h_map =>
    intro X Y
    simp only [relabelEnrichedObjects, eqToHom_refl, Category.comp_id]
    change F.map X Y ≫ 𝟙 _ = F.map X Y
    exact Category.comp_id _

end Enriched

section Ordinary
variable {C : Type v} {D : Type w} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D]

/-- 同じ元の通常射の全 Hom 表示は、対象座標の等号に沿う同じ射として回収される。 -/
theorem relabelEnrichedObjects_hom
    (F : EnrichedFunctor SSet.{u} C D) (obj : C → D) (h : F.obj = obj)
    {X Y : C} (f : X ⟶ Y) (g : F.obj X ⟶ F.obj Y)
    (hg : eHomEquiv SSet f ≫ F.map X Y = eHomEquiv SSet g) :
    eHomEquiv SSet f ≫ (relabelEnrichedObjects F obj h).map X Y =
      eHomEquiv SSet (eqToHom (congrArg (fun k : C → D => k X) h).symm ≫
        g ≫ eqToHom (congrArg (fun k : C → D => k Y) h)) := by
  cases h
  simpa only [relabelEnrichedObjects, eqToHom_refl, Category.comp_id, Category.id_comp] using hg

end Ordinary

section Evaluation
open SerrePositivity.KST.SConstruction
variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- 全パラメータの評価は、始域と終域を同じ対象等号で輸送した元の評価射。 -/
theorem relabelEnrichedObjects_uncurry
    (F : EnrichedFunctor SSet.{u} C SSetInternalObject.{u})
    (obj : C → SSetInternalObject.{u}) (h : F.obj = obj)
    {X Y : C} {P : SSet.{u}} (H : P ⟶ (X ⟶[SSet.{u}] Y)) :
    uncurry (H ≫ (relabelEnrichedObjects F obj h).map X Y) =
      (eqToHom (congrArg (fun k : C → SSetInternalObject.{u} => (k X).obj) h).symm ▷ P) ≫
        uncurry (H ≫ F.map X Y) ≫
          eqToHom (congrArg (fun k : C → SSetInternalObject.{u} => (k Y).obj) h) := by
  cases h
  simp only [relabelEnrichedObjects, eqToHom_refl, Category.comp_id,
    id_whiskerRight, Category.id_comp]
  rfl

end Evaluation
end SerrePositivity.KST.Fibration
