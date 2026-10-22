module
public import SerrePositivity.KST.SConstruction.PointedEnrichedSpanFunctor
public import SerrePositivity.KST.SConstruction.PointedSpanPushoutEnrichedFunctor
public import SerrePositivity.KST.SConstruction.PointedTensorCylinderTransformation
public import SerrePositivity.KST.SConstruction.PointedTensorMappingCylinder

/-! # 同じ点つき実写像円柱への厳密単体的豊穣関手
概要：厳密豊穣関手間の元の全 Hom に自然な射を、同じ実写像円柱へ関手的に送る。
方針：零端と元の射の span を標準 end に束ね、同じ実押し出し関手で後合成する。
規約：全 Hom の自然性を保ち、元の実押し出しと値が一致。使われ方：関手的 BF 置換。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- 元の豊穣関手に前合成した円柱零端も、全 Hom に厳密に自然。 -/
lemma pointedEnrichedMappingCylinderEnd_whisker
    (F : EnrichedFunctor SSet.{u} C PointedSSetObject.{u}) (X Y : C) :
    F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (pointedTensorCylinderEnd 0 (F.obj Y)) =
      (F.comp SSet pointedTensorCylinderFunctor).map X Y ≫
        eHomWhiskerRight SSet (pointedTensorCylinderEnd 0 (F.obj X))
          (pointedTensorCylinderFunctor.obj (F.obj Y)) := by
  change F.map X Y ≫ _ =
    (F.map X Y ≫ pointedTensorCylinderFunctor.map (F.obj X) (F.obj Y)) ≫ _
  rw [Category.assoc, ← pointedTensorCylinderEnd_whisker 0 (F.obj X) (F.obj Y)]

variable (F G : EnrichedFunctor SSet.{u} C PointedSSetObject.{u})
  (t : ∀ X, F.obj X ⟶ G.obj X)
  (h : ∀ X Y, F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (t Y) =
    G.map X Y ≫ eHomWhiskerRight SSet (t X) (G.obj Y))

/-- 元の零端と全 Hom に自然な同じ射からなる、実円柱 span の豊穣関手。 -/
def pointedEnrichedMappingCylinderSpan : EnrichedFunctor SSet.{u} C PointedSpanDiagram.{u} :=
  pointedEnrichedSpanFunctor F (F.comp SSet pointedTensorCylinderFunctor) G
    (fun X => pointedTensorCylinderEnd 0 (F.obj X)) t
    (pointedEnrichedMappingCylinderEnd_whisker F) h

/-- 元の実写像円柱そのものを値とする、厳密単体的豊穣関手。 -/
def pointedEnrichedMappingCylinderFunctor :
    EnrichedFunctor SSet.{u} C PointedSSetObject.{u} :=
  (pointedEnrichedMappingCylinderSpan F G t h).comp SSet pointedSpanPushoutEnrichedFunctor

/-- 豊穣関手の実値は、同じ元の射を使う実写像円柱そのもの。 -/
lemma pointedEnrichedMappingCylinderFunctor_obj (X : C) :
    ((pointedEnrichedMappingCylinderFunctor F G t h).obj X).obj =
      pointedTensorMappingCylinder (show (F.obj X).obj ⟶ (G.obj X).obj from t X) := rfl

end SerrePositivity.KST.SConstruction
