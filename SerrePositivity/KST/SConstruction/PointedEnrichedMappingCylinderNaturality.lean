module
public import SerrePositivity.KST.SConstruction.PointedEnrichedMappingCylinderComponents
public import SerrePositivity.KST.SConstruction.PointedSpanPushoutDescNaturality

/-! # 同じ写像円柱の実成分の全 Hom 自然性
概要：元の円柱包含・標的包含・源比較・射影を、全単体的入力に自然にする。
方針：標準 end の射影回収と実押し出しの余錐降下を使う。
規約：通常射も全高次入力も変更しない。使われ方：厳密 dg 入力の BF 比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet
variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- 元の全 Hom 作用に前合成しても、円柱の任意の指定端点は自然。 -/
lemma pointedEnrichedCylinderEnd_whisker
    (F : EnrichedFunctor SSet.{u} C PointedSSetObject.{u}) (i : Fin 2) (X Y : C) :
    F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (pointedTensorCylinderEnd i (F.obj Y)) =
      (F.comp SSet pointedTensorCylinderFunctor).map X Y ≫
        eHomWhiskerRight SSet (pointedTensorCylinderEnd i (F.obj X))
          (pointedTensorCylinderFunctor.obj (F.obj Y)) := by
  change F.map X Y ≫ _ =
    (F.map X Y ≫ pointedTensorCylinderFunctor.map (F.obj X) (F.obj Y)) ≫ _
  rw [Category.assoc, ← pointedTensorCylinderEnd_whisker i (F.obj X) (F.obj Y)]

/-- 元の全 Hom 作用に前合成しても、同じ円柱射影は自然。 -/
lemma pointedEnrichedCylinderProjection_whisker
    (F : EnrichedFunctor SSet.{u} C PointedSSetObject.{u}) (X Y : C) :
    (F.comp SSet pointedTensorCylinderFunctor).map X Y ≫
        eHomWhiskerLeft SSet (pointedTensorCylinderFunctor.obj (F.obj X))
          (pointedTensorCylinderProjection (F.obj Y)) =
      F.map X Y ≫ eHomWhiskerRight SSet (pointedTensorCylinderProjection (F.obj X)) (F.obj Y) := by
  change (F.map X Y ≫ pointedTensorCylinderFunctor.map (F.obj X) (F.obj Y)) ≫
      eHomWhiskerLeft SSet (pointedTensorCylinderFunctor.obj (F.obj X))
        (pointedTensorCylinderProjection (F.obj Y)) =
    F.map X Y ≫ eHomWhiskerRight SSet (pointedTensorCylinderProjection (F.obj X)) (F.obj Y)
  rw [Category.assoc, pointedTensorCylinderProjection_whisker (F.obj X) (F.obj Y)]

variable (F G : EnrichedFunctor SSet.{u} C PointedSSetObject.{u})
  (t : ∀ X, F.obj X ⟶ G.obj X)
  (h : ∀ X Y, F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X) (t Y) =
    G.map X Y ≫ eHomWhiskerRight SSet (t X) (G.obj Y))

/-- 円柱 span の左射影は、元の円柱上の同じ全 Hom 作用を回収する。 -/
lemma pointedEnrichedMappingCylinderSpan_left (X Y : C) :
    (pointedEnrichedMappingCylinderSpan F G t h).map X Y ≫
        pointedSpanProjection ((pointedEnrichedMappingCylinderSpan F G t h).obj X)
          ((pointedEnrichedMappingCylinderSpan F G t h).obj Y) .left =
      (F.comp SSet pointedTensorCylinderFunctor).map X Y :=
  pointedEnrichedSpanHom_projection F (F.comp SSet pointedTensorCylinderFunctor) G
    (fun X => pointedTensorCylinderEnd 0 (F.obj X)) t
    (pointedEnrichedMappingCylinderEnd_whisker F) h X Y .left

/-- 円柱 span の右射影は、元の標的の同じ全 Hom 作用を回収する。 -/
lemma pointedEnrichedMappingCylinderSpan_right (X Y : C) :
    (pointedEnrichedMappingCylinderSpan F G t h).map X Y ≫
        pointedSpanProjection ((pointedEnrichedMappingCylinderSpan F G t h).obj X)
          ((pointedEnrichedMappingCylinderSpan F G t h).obj Y) .right = G.map X Y :=
  pointedEnrichedSpanHom_projection F (F.comp SSet pointedTensorCylinderFunctor) G
    (fun X => pointedTensorCylinderEnd 0 (F.obj X)) t
    (pointedEnrichedMappingCylinderEnd_whisker F) h X Y .right

/-- 同じ元の円柱包含は、全 Hom に厳密に自然。 -/
lemma pointedEnrichedMappingCylinderCylinder_whisker (X Y : C) :
    (F.comp SSet pointedTensorCylinderFunctor).map X Y ≫
        eHomWhiskerLeft SSet (pointedTensorCylinderFunctor.obj (F.obj X))
          (pointedEnrichedMappingCylinderCylinder F G t h Y) =
      (pointedEnrichedMappingCylinderFunctor F G t h).map X Y ≫
        eHomWhiskerRight SSet (pointedEnrichedMappingCylinderCylinder F G t h X)
          ((pointedEnrichedMappingCylinderFunctor F G t h).obj Y) := by
  have hm := pointedEnrichedSpanPushout_inl (pointedEnrichedMappingCylinderSpan F G t h) X Y
  rw [← Category.assoc, pointedEnrichedMappingCylinderSpan_left F G t h X Y] at hm
  exact hm.symm

/-- 同じ元の標的包含は、全 Hom に厳密に自然。 -/
lemma pointedEnrichedMappingCylinderTarget_whisker (X Y : C) :
    G.map X Y ≫ eHomWhiskerLeft SSet (G.obj X)
        (pointedEnrichedMappingCylinderTarget F G t h Y) =
      (pointedEnrichedMappingCylinderFunctor F G t h).map X Y ≫
        eHomWhiskerRight SSet (pointedEnrichedMappingCylinderTarget F G t h X)
          ((pointedEnrichedMappingCylinderFunctor F G t h).obj Y) := by
  have hm := pointedEnrichedSpanPushout_inr (pointedEnrichedMappingCylinderSpan F G t h) X Y
  rw [← Category.assoc, pointedEnrichedMappingCylinderSpan_right F G t h X Y] at hm
  exact hm.symm

/-- 元の一端を使う同じ源比較は、全 Hom に厳密に自然。 -/
lemma pointedEnrichedMappingCylinderSource_whisker (X Y : C) :
    F.map X Y ≫ eHomWhiskerLeft SSet (F.obj X)
        (pointedEnrichedMappingCylinderSource F G t h Y) =
      (pointedEnrichedMappingCylinderFunctor F G t h).map X Y ≫
        eHomWhiskerRight SSet (pointedEnrichedMappingCylinderSource F G t h X)
          ((pointedEnrichedMappingCylinderFunctor F G t h).obj Y) :=
  enriched_whisker_naturality_comp SSet (F.map X Y)
    ((F.comp SSet pointedTensorCylinderFunctor).map X Y)
    ((pointedEnrichedMappingCylinderFunctor F G t h).map X Y)
    (pointedTensorCylinderEnd 1 (F.obj X)) (pointedTensorCylinderEnd 1 (F.obj Y))
    (pointedEnrichedMappingCylinderCylinder F G t h X)
    (pointedEnrichedMappingCylinderCylinder F G t h Y)
    (pointedEnrichedCylinderEnd_whisker F 1 X Y)
    (pointedEnrichedMappingCylinderCylinder_whisker F G t h X Y)

/-- 同じ元の写像円柱射影は、全 Hom に厳密に自然。 -/
lemma pointedEnrichedMappingCylinderProjection_whisker (X Y : C) :
    (pointedEnrichedMappingCylinderFunctor F G t h).map X Y ≫
        eHomWhiskerLeft SSet ((pointedEnrichedMappingCylinderFunctor F G t h).obj X)
          (pointedEnrichedMappingCylinderProjection F G t h Y) =
      G.map X Y ≫ eHomWhiskerRight SSet
        (pointedEnrichedMappingCylinderProjection F G t h X) (G.obj Y) := by
  apply pointedEnrichedSpanPushoutDesc_whisker
    (pointedEnrichedMappingCylinderSpan F G t h) G
    (fun X => pointedTensorCylinderProjection (F.obj X) ≫ t X) (fun X => 𝟙 (G.obj X))
    (pointedEnrichedMappingCylinder_projection_condition F G t)
  · intro X Y
    rw [pointedEnrichedMappingCylinderSpan_left F G t h X Y]
    exact enriched_whisker_naturality_comp SSet
      ((F.comp SSet pointedTensorCylinderFunctor).map X Y) (F.map X Y) (G.map X Y)
      (pointedTensorCylinderProjection (F.obj X)) (pointedTensorCylinderProjection (F.obj Y))
      (t X) (t Y) (pointedEnrichedCylinderProjection_whisker F X Y) (h X Y)
  · intro X Y
    rw [pointedEnrichedMappingCylinderSpan_right F G t h X Y]
    change G.map X Y ≫ eHomWhiskerLeft SSet (G.obj X) (𝟙 (G.obj Y)) =
      G.map X Y ≫ eHomWhiskerRight SSet (𝟙 (G.obj X)) (G.obj Y)
    rw [eHomWhiskerLeft_id, eHomWhiskerRight_id]

end SerrePositivity.KST.SConstruction
