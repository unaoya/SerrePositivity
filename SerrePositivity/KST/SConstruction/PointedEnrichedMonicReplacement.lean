module
public import SerrePositivity.KST.SConstruction.PointedEnrichedMappingCylinderNaturality
public import SerrePositivity.KST.SConstruction.ExInfinityPointedUnitWhisker

/-! # 元の全 Hom 自然な射の関手的 Kan 単射置換
概要：元の実写像円柱を同じ Ex∞ へ送り、源と標的の実比較を保持する。
方針：同じ円柱の厳密豊穣関手と Ex∞ の厳密豊穣関手を合成する。
規約：入力の射は単射でなくてよい。使われ方：BF 最初の評価と帰納段。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
variable {C : Type v} [EnrichedCategory SSet.{u} C]
  (F G : EnrichedFunctor SSet.{u} C PointedSSetObject.{u})
  (t : ∀ X, F.obj X ⟶ G.obj X)
  (h : ∀ X Y, F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (t Y) =
    G.map X Y ≫ eHomWhiskerRight SSet (t X) (G.obj Y))

/-- 同じ元の実写像円柱を Ex∞ へ送る標準点つき厳密豊穣関手。 -/
def pointedEnrichedMonicReplacementFunctor :
    EnrichedFunctor SSet.{u} C PointedSSetObject.{u} :=
  (pointedEnrichedMappingCylinderFunctor F G t h).comp SSet exInfinityPointedEnrichedFunctor

/-- 同じ値と全 Hom を、Kan 対象の全部分圏へ束ねた厳密豊穣関手。 -/
def pointedEnrichedMonicReplacementKanFunctor :
    EnrichedFunctor SSet.{u} C PointedKanObject.{u} :=
  (pointedEnrichedMappingCylinderFunctor F G t h).comp SSet exInfinityPointedKanEnrichedFunctor

/-- 元の実写像円柱から同じ Kan 置換への単位成分。 -/
def pointedEnrichedMonicReplacementUnit (X : C) :
    (pointedEnrichedMappingCylinderFunctor F G t h).obj X ⟶
      (pointedEnrichedMonicReplacementFunctor F G t h).obj X :=
  exInfinityPointedUnit ((pointedEnrichedMappingCylinderFunctor F G t h).obj X)

/-- 元の源からの比較は、同じ実円柱源射と単位の合成。 -/
def pointedEnrichedMonicReplacementSource (X : C) :
    F.obj X ⟶ (pointedEnrichedMonicReplacementFunctor F G t h).obj X :=
  pointedEnrichedMappingCylinderSource F G t h X ≫ pointedEnrichedMonicReplacementUnit F G t h X

/-- 元の標的からの比較は、同じ実円柱標的包含と単位の合成。 -/
def pointedEnrichedMonicReplacementTarget (X : C) :
    G.obj X ⟶ (pointedEnrichedMonicReplacementFunctor F G t h).obj X :=
  pointedEnrichedMappingCylinderTarget F G t h X ≫ pointedEnrichedMonicReplacementUnit F G t h X

end SerrePositivity.KST.SConstruction
