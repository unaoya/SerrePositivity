module
public import SerrePositivity.KST.SConstruction.PointedSSetObject
public import SerrePositivity.KST.SConstruction.PointedKanEnrichedObjects

/-! # 標準点つき豊穣関手の Kan 値への持ち上げ
概要：同じ元の点つき値と全 basedHom を、Kan な対象の全部分圏に保持する。
方針：対象の Kan 性だけを束ね、既存の標準豊穣の全 Hom 作用と法則を使う。
規約：通常の射も全高次入力も変更しない。使われ方：Ex∞ と γ1 の接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  (F : EnrichedFunctor SSet.{u} C PointedSSetObject.{u})
  (hF : ∀ X, KanComplex (F.obj X).obj.right)

/-- 元の点つき実値と全 basedHom を保持する、Kan 全部分圏への厳密豊穣関手。 -/
def pointedEnrichedKanLift : EnrichedFunctor SSet.{u} C PointedKanObject.{u} where
  obj X := ⟨(F.obj X).obj, hF X⟩
  map := F.map
  map_id := F.map_id
  map_comp := F.map_comp

/-- 元の通常射の標準表示は、同じ元の基点固定射を持つ Kan 射として回収される。 -/
lemma pointedEnrichedKanLift_hom {X Y : C} (f : X ⟶ Y) (g : F.obj X ⟶ F.obj Y)
    (h : eHomEquiv SSet.{u} f ≫ F.map X Y = eHomEquiv SSet.{u} g) :
    eHomEquiv SSet.{u} f ≫ (pointedEnrichedKanLift F hF).map X Y =
      eHomEquiv SSet.{u}
        (show (pointedEnrichedKanLift F hF).obj X ⟶ (pointedEnrichedKanLift F hF).obj Y from
          ObjectProperty.homMk (show (F.obj X).obj ⟶ (F.obj Y).obj from g)) := h

end SerrePositivity.KST.SConstruction
