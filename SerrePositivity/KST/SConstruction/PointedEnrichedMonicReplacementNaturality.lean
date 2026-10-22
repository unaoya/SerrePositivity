module
public import SerrePositivity.KST.SConstruction.PointedEnrichedMonicReplacement

/-! # 同じ Kan 単射置換の全 Hom 自然性
概要：元の全 Hom 自然な射から作る実置換の単位・源・標的比較は全 Hom に自然。
方針：同じ写像円柱の全 Hom 自然性へ、同じ Ex∞ 単位の自然性を合成する。
規約：元の実成分と全入力族を保持。使われ方：BF の厳密豊穣構造射。
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

/-- 同じ元の実写像円柱から Ex∞ 値への単位は、全 Hom に自然。 -/
lemma pointedEnrichedMonicReplacementUnit_whisker (X Y : C) :
    (pointedEnrichedMappingCylinderFunctor F G t h).map X Y ≫
        eHomWhiskerLeft SSet ((pointedEnrichedMappingCylinderFunctor F G t h).obj X)
          (pointedEnrichedMonicReplacementUnit F G t h Y) =
      (pointedEnrichedMonicReplacementFunctor F G t h).map X Y ≫
        eHomWhiskerRight SSet (pointedEnrichedMonicReplacementUnit F G t h X)
          ((pointedEnrichedMonicReplacementFunctor F G t h).obj Y) :=
  enrichedExInfinityPointedUnit_whisker (pointedEnrichedMappingCylinderFunctor F G t h) X Y

/-- 同じ元の源から Kan 置換への比較は、全 Hom に自然。 -/
lemma pointedEnrichedMonicReplacementSource_whisker (X Y : C) :
    F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X)
        (pointedEnrichedMonicReplacementSource F G t h Y) =
      (pointedEnrichedMonicReplacementFunctor F G t h).map X Y ≫
        eHomWhiskerRight SSet (pointedEnrichedMonicReplacementSource F G t h X)
          ((pointedEnrichedMonicReplacementFunctor F G t h).obj Y) :=
  enriched_whisker_naturality_comp SSet (F.map X Y)
    ((pointedEnrichedMappingCylinderFunctor F G t h).map X Y)
    ((pointedEnrichedMonicReplacementFunctor F G t h).map X Y)
    (pointedEnrichedMappingCylinderSource F G t h X)
    (pointedEnrichedMappingCylinderSource F G t h Y)
    (pointedEnrichedMonicReplacementUnit F G t h X)
    (pointedEnrichedMonicReplacementUnit F G t h Y)
    (pointedEnrichedMappingCylinderSource_whisker F G t h X Y)
    (pointedEnrichedMonicReplacementUnit_whisker F G t h X Y)

/-- 同じ元の標的から Kan 置換への比較も、全 Hom に自然。 -/
lemma pointedEnrichedMonicReplacementTarget_whisker (X Y : C) :
    G.map X Y ≫ eHomWhiskerLeft SSet (G.obj X)
        (pointedEnrichedMonicReplacementTarget F G t h Y) =
      (pointedEnrichedMonicReplacementFunctor F G t h).map X Y ≫
        eHomWhiskerRight SSet (pointedEnrichedMonicReplacementTarget F G t h X)
          ((pointedEnrichedMonicReplacementFunctor F G t h).obj Y) :=
  enriched_whisker_naturality_comp SSet (G.map X Y)
    ((pointedEnrichedMappingCylinderFunctor F G t h).map X Y)
    ((pointedEnrichedMonicReplacementFunctor F G t h).map X Y)
    (pointedEnrichedMappingCylinderTarget F G t h X)
    (pointedEnrichedMappingCylinderTarget F G t h Y)
    (pointedEnrichedMonicReplacementUnit F G t h X)
    (pointedEnrichedMonicReplacementUnit F G t h Y)
    (pointedEnrichedMappingCylinderTarget_whisker F G t h X Y)
    (pointedEnrichedMonicReplacementUnit_whisker F G t h X Y)

end SerrePositivity.KST.SConstruction
