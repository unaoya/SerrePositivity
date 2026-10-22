module
public import SerrePositivity.KST.SConstruction.PointedTensorMappingCylinderMono

/-! # 同じ二脚写像円柱の両標的を保つ単射
概要：一方の写像円柱の残る端を他方の脚に貼り付けても、元の両標的は単射で残る。
方針：源・標的の和の単射を入れ替え、同じ元の押し出しで両標的の和を単射にする。
規約：同じ元の押し出しを保持。使われ方：BF の構造射の単射性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet

/-- 点つき余積の二成分を入れ替えても、同じ和の基礎単射性を保つ。 -/
lemma pointedCoprodDesc_flip_mono {A B Z : PointedSimplicialSet.{u}}
    (a : A ⟶ Z) (b : B ⟶ Z) [Mono (coprod.desc a b).right] :
    Mono (coprod.desc b a).right := by
  let i : B ⨿ A ⟶ A ⨿ B := (coprod.braiding B A).hom
  have hf : coprod.desc b a = i ≫ coprod.desc a b := by
    apply coprod.hom_ext <;> simp [i]
  rw [hf]
  let _ : IsSplitMono i.right := IsSplitMono.mk'
    ⟨(coprod.braiding B A).inv.right,
      congrArg Under.Hom.right (coprod.braiding B A).hom_inv_id⟩
  change Mono (i.right ≫ (coprod.desc a b).right)
  infer_instance

/-- 元の両標的の和から、同じ写像円柱を貼り付けた実押し出しへの比較。 -/
def pointedDoubleMappingCylinderPair {X A B : PointedSimplicialSet.{u}}
    (f : X ⟶ A) (g : X ⟶ B) :
    A ⨿ B ⟶ pushout (pointedTensorMappingCylinderSource f) g :=
  coproductAttachmentComparison (pointedTensorMappingCylinderTarget f)
    (pointedTensorMappingCylinderSource f) g

/-- 同じ貼り付け押し出しは、元の標的・源の和からの押し出しでもある。 -/
lemma pointedDoubleMappingCylinderPair_isPushout {X A B : PointedSimplicialSet.{u}}
    (f : X ⟶ A) (g : X ⟶ B) :
    IsPushout (coprod.desc (pointedTensorMappingCylinderTarget f)
        (pointedTensorMappingCylinderSource f)) (coprod.map (𝟙 A) g)
      (pushout.inl (pointedTensorMappingCylinderSource f) g)
      (pointedDoubleMappingCylinderPair f g) :=
  coproductAttachment_isPushout (pointedTensorMappingCylinderTarget f)
    (pointedTensorMappingCylinderSource f) g

/-- 同じ元の両標的の和は、貼り付け押し出しへ基礎単射で入る。 -/
instance pointedDoubleMappingCylinderPair_mono {X A B : PointedSimplicialSet.{u}}
    (f : X ⟶ A) (g : X ⟶ B) : Mono (pointedDoubleMappingCylinderPair f g).right := by
  let _ : Mono (coprod.desc (pointedTensorMappingCylinderSource f)
      (pointedTensorMappingCylinderTarget f)).right := pointedTensorMappingCylinderPair_mono f
  let _ : Mono (coprod.desc (pointedTensorMappingCylinderTarget f)
      (pointedTensorMappingCylinderSource f)).right :=
    pointedCoprodDesc_flip_mono (pointedTensorMappingCylinderSource f)
      (pointedTensorMappingCylinderTarget f)
  exact pointedIsPushout_mono_right (pointedDoubleMappingCylinderPair_isPushout f g)

/-- 元の左標的は、同じ貼り付け押し出しへ基礎単射で入る。 -/
instance pointedDoubleMappingCylinderLeft_mono {X A B : PointedSimplicialSet.{u}}
    (f : X ⟶ A) (g : X ⟶ B) :
    Mono (pointedTensorMappingCylinderTarget f ≫
      pushout.inl (pointedTensorMappingCylinderSource f) g).right := by
  have hf : pointedTensorMappingCylinderTarget f ≫
        pushout.inl (pointedTensorMappingCylinderSource f) g =
      (coprod.inl : A ⟶ A ⨿ B) ≫ pointedDoubleMappingCylinderPair f g :=
    (coprod.inl_desc _ _).symm
  rw [hf]
  change Mono ((coprod.inl : A ⟶ A ⨿ B).right ≫ (pointedDoubleMappingCylinderPair f g).right)
  infer_instance

/-- 元の右標的も、同じ貼り付け押し出しへ基礎単射で入る。 -/
instance pointedDoubleMappingCylinderRight_mono {X A B : PointedSimplicialSet.{u}}
    (f : X ⟶ A) (g : X ⟶ B) :
    Mono (pushout.inr (pointedTensorMappingCylinderSource f) g).right :=
  pointedPushout_inr_mono (pointedTensorMappingCylinderSource f) g

end SerrePositivity.KST.SConstruction
