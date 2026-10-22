module
public import SerrePositivity.KST.SConstruction.PointedSpanPushoutDesc
public import SerrePositivity.KST.SConstruction.EnrichedWhiskerNaturality

/-! # 同じ実押し出しの余錐降下の全 Hom 自然性
概要：元の両余錐成分に自然な全族は、同じ押し出しからの降下にも自然である。
方針：両包含で全族の等号を検出し、前後合成の交換で元の自然性へ戻す。
規約：通常射だけの自然性には制限しない。使われ方：実写像円柱の射影。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet
variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- 元の両脚の全 Hom 自然性は、同じ実押し出しからの降下に移る。 -/
lemma pointedEnrichedSpanPushoutDesc_whisker
    (F : EnrichedFunctor SSet.{u} C PointedSpanDiagram.{u})
    (G : EnrichedFunctor SSet.{u} C PointedSSetObject.{u})
    (l : ∀ X, (F.obj X).diagram.obj .left ⟶ G.obj X)
    (r : ∀ X, (F.obj X).diagram.obj .right ⟶ G.obj X)
    (w : ∀ X, (F.obj X).diagram.map WalkingSpan.Hom.fst ≫ l X =
      (F.obj X).diagram.map WalkingSpan.Hom.snd ≫ r X)
    (hl : ∀ X Y, (F.map X Y ≫ pointedSpanProjection (F.obj X) (F.obj Y) .left) ≫
        eHomWhiskerLeft SSet ((F.obj X).diagram.obj .left) (l Y) =
      G.map X Y ≫ eHomWhiskerRight SSet (l X) (G.obj Y))
    (hr : ∀ X Y, (F.map X Y ≫ pointedSpanProjection (F.obj X) (F.obj Y) .right) ≫
        eHomWhiskerLeft SSet ((F.obj X).diagram.obj .right) (r Y) =
      G.map X Y ≫ eHomWhiskerRight SSet (r X) (G.obj Y)) (X Y : C) :
    (F.comp SSet pointedSpanPushoutEnrichedFunctor).map X Y ≫
        eHomWhiskerLeft SSet (pointedSpanPushout (F.obj X))
          (pointedSpanPushoutDesc (F.obj Y) (G.obj Y) (l Y) (r Y) (w Y)) =
      G.map X Y ≫ eHomWhiskerRight SSet
        (pointedSpanPushoutDesc (F.obj X) (G.obj X) (l X) (r X) (w X)) (G.obj Y) := by
  apply pointedSpanPushoutHom_ext (F.obj X) (G.obj Y)
  · exact enriched_cocone_desc_family SSet
      (F.map X Y ≫ pointedSpanProjection (F.obj X) (F.obj Y) .left)
      (F.map X Y ≫ pointedSpanPushoutHom (F.obj X) (F.obj Y)) (G.map X Y)
      (pointedSpanPushoutInl (F.obj X)) (pointedSpanPushoutInl (F.obj Y))
      (pointedSpanPushoutDesc (F.obj X) (G.obj X) (l X) (r X) (w X))
      (pointedSpanPushoutDesc (F.obj Y) (G.obj Y) (l Y) (r Y) (w Y))
      (by
        rw [Category.assoc, pointedSpanPushoutHom_inl (F.obj X) (F.obj Y)]
        rfl)
      (by
        erw [pointedSpanPushoutInl_desc (F.obj Y) (G.obj Y) (l Y) (r Y) (w Y),
          pointedSpanPushoutInl_desc (F.obj X) (G.obj X) (l X) (r X) (w X)]
        exact hl X Y)
  · exact enriched_cocone_desc_family SSet
      (F.map X Y ≫ pointedSpanProjection (F.obj X) (F.obj Y) .right)
      (F.map X Y ≫ pointedSpanPushoutHom (F.obj X) (F.obj Y)) (G.map X Y)
      (pointedSpanPushoutInr (F.obj X)) (pointedSpanPushoutInr (F.obj Y))
      (pointedSpanPushoutDesc (F.obj X) (G.obj X) (l X) (r X) (w X))
      (pointedSpanPushoutDesc (F.obj Y) (G.obj Y) (l Y) (r Y) (w Y))
      (by
        rw [Category.assoc, pointedSpanPushoutHom_inr (F.obj X) (F.obj Y)]
        rfl)
      (by
        erw [pointedSpanPushoutInr_desc (F.obj Y) (G.obj Y) (l Y) (r Y) (w Y),
          pointedSpanPushoutInr_desc (F.obj X) (G.obj X) (l X) (r X) (w X)]
        exact hr X Y)

end SerrePositivity.KST.SConstruction
