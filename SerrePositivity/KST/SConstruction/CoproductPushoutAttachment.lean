module
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-! # 一方の端を貼り付けた押し出しを両端の和から見る
概要：一方の脚を貼り付ける押し出しは、両脚の余積射からの押し出しでもある。
方針：元の押し出しと余積の普遍性を順に使い、同じ射を回収する。
規約：同じ元の押し出し対象を使う。使われ方：写像円柱源比較の単射性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits
variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
  {W X Y Z : C} (a : W ⟶ Z) (b : X ⟶ Z) (f : X ⟶ Y) [HasPushout b f]

/-- 貼り付け後の、残った端と標的の和からの同じ実比較射。 -/
def coproductAttachmentComparison : W ⨿ Y ⟶ pushout b f :=
  coprod.desc (a ≫ pushout.inl b f) (pushout.inr b f)

/-- 元の両脚と貼り付け射は、同じ比較射に関して可換。 -/
lemma coproductAttachment_condition :
    coprod.desc a b ≫ pushout.inl b f =
      coprod.map (𝟙 W) f ≫ coproductAttachmentComparison a b f := by
  apply coprod.hom_ext
  · simp only [coprod.inl_desc_assoc, coprod.inl_map_assoc, Category.id_comp,
      coproductAttachmentComparison, coprod.inl_desc]
  · simp only [coprod.inr_desc_assoc, coprod.inr_map_assoc,
      coproductAttachmentComparison, coprod.inr_desc]
    exact pushout.condition

omit [HasPushout b f] in
/-- 余積での整合条件の、貼り付け側の元の脚への制限。 -/
lemma coproductAttachment_desc_condition
    (s : PushoutCocone (coprod.desc a b) (coprod.map (𝟙 W) f)) :
    b ≫ s.inl = f ≫ ((coprod.inr : Y ⟶ W ⨿ Y) ≫ s.inr) := by
  have h := congrArg (fun k => (coprod.inr : X ⟶ W ⨿ X) ≫ k) s.condition
  simpa only [coprod.inr_desc_assoc, coprod.inr_map_assoc, Category.assoc] using h

/-- 元の押し出しから、両端和について整合する余錐への実降下。 -/
def coproductAttachmentDesc
    (s : PushoutCocone (coprod.desc a b) (coprod.map (𝟙 W) f)) : pushout b f ⟶ s.pt :=
  pushout.desc s.inl ((coprod.inr : Y ⟶ W ⨿ Y) ≫ s.inr)
    (coproductAttachment_desc_condition a b f s)

/-- 同じ元の一端貼り付け押し出しは、両端和からの押し出しでもある。 -/
lemma coproductAttachment_isPushout :
    IsPushout (coprod.desc a b) (coprod.map (𝟙 W) f) (pushout.inl b f)
      (coproductAttachmentComparison a b f) := by
  refine IsPushout.of_isColimit
    (c := PushoutCocone.mk _ _ (coproductAttachment_condition a b f)) ?_
  refine PushoutCocone.IsColimit.mk _ (fun s => coproductAttachmentDesc a b f s) ?_ ?_ ?_
  · intro s
    exact pushout.inl_desc _ _ _
  · intro s
    apply coprod.hom_ext
    · rw [coproductAttachmentComparison, coprod.inl_desc_assoc, Category.assoc,
        coproductAttachmentDesc, pushout.inl_desc]
      have h := congrArg (fun k => (coprod.inl : W ⟶ W ⨿ X) ≫ k) s.condition
      simpa only [coprod.inl_desc_assoc, coprod.inl_map_assoc,
        Category.id_comp, Category.assoc] using h
    · rw [coproductAttachmentComparison, coprod.inr_desc_assoc,
        coproductAttachmentDesc, pushout.inr_desc]
  · intro s m hl hr
    apply pushout.hom_ext
    · rw [coproductAttachmentDesc, pushout.inl_desc]
      exact hl
    · rw [coproductAttachmentDesc, pushout.inr_desc]
      have h := congrArg (fun k => (coprod.inr : Y ⟶ W ⨿ Y) ≫ k) hr
      simpa only [coproductAttachmentComparison, coprod.inr_desc_assoc, Category.assoc] using h

end SerrePositivity.KST.SConstruction
