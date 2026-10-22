module
public import SerrePositivity.KST.Fibration.InitialHornPoint
public import SerrePositivity.InfinityCategories.Core.InnerAnodyneEquivalence

/-! # 先行錐と最後の辺の元の貼り合わせ

任意の A に対し A⋆Λ¹₀ と最後の Δ¹ を貼る。元の A⋆Δ¹ への包含は inner anodyne。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 先行錐と最後の一辺の全単体を保持する部分複体。 -/
def tailAttachment (A : SSet.{u}) : (join A (Δ[1] : SSet.{u})).Subcomplex :=
  joinUnion (⊥ : A.Subcomplex) (horn 1 0)

/-- 貼り合わせから元の全 join への包含は inner anodyne。 -/
lemma tailAttachment_innerAnodyne (A : SSet.{u}) :
    innerAnodyneExtensions (tailAttachment A).ι :=
  joinUnion_innerAnodyne_of_leftAnodyne _ _ (leftAnodyneExtensions_horn 0 (by decide))

/-- 最後の元の辺を貼り合わせに含める。 -/
def tailAttachmentEdge (A : SSet.{u}) : (Δ[1] : SSet.{u}) ⟶ (tailAttachment A : SSet.{u}) :=
  (emptyJoinIso A (Δ[1] : SSet.{u})).inv ≫ joinUnionLeft (⊥ : A.Subcomplex) (horn 1 0)

/-- 元の先行錐を貼り合わせに含める。 -/
def tailAttachmentPrefix (A : SSet.{u}) :
    join A (Λ[1, 0] : SSet.{u}) ⟶ (tailAttachment A : SSet.{u}) :=
  joinUnionRight (⊥ : A.Subcomplex) (horn 1 0)

/-- 貼り合わせの普遍性は、元の共有始点と二つの包含で与えられる。 -/
theorem tailAttachment_isPushout (A : SSet.{u}) :
    IsPushout (horn 1 0).ι (joinInr A (Λ[1, 0] : SSet.{u}))
      (tailAttachmentEdge A) (tailAttachmentPrefix A) := by
  apply (joinUnion_isPushout (⊥ : A.Subcomplex) (horn 1 0)).of_iso
    (emptyJoinIso A (Λ[1, 0] : SSet.{u})) (emptyJoinIso A (Δ[1] : SSet.{u}))
    (Iso.refl _) (Iso.refl _)
  · apply (cancel_epi (emptyJoinIso A (Λ[1, 0] : SSet.{u})).inv).1
    change joinInr _ _ ≫ joinMap (𝟙 _) (horn 1 0).ι ≫ _ = _
    rw [← Category.assoc, joinInr_joinMap, Category.assoc]
    simp [← Category.assoc, emptyJoinIso]
  · apply (cancel_epi (emptyJoinIso A (Λ[1, 0] : SSet.{u})).inv).1
    change joinInr _ _ ≫ (joinMap (⊥ : A.Subcomplex).ι (𝟙 _) ≫ 𝟙 _) = _
    rw [Category.comp_id, joinInr_joinMap, Category.id_comp]
    simp [← Category.assoc, emptyJoinIso]
  · change _ ≫ 𝟙 _ = _ ≫ ((emptyJoinIso A (Δ[1] : SSet.{u})).inv ≫ _)
    simp only [Category.comp_id, Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

/-- 元の全図式から貼り合わせへの制限は全境界持ち上げを持つ。 -/
lemma tailAttachment_pre_trivialKanFibration (A B : SSet.{u}) [Quasicategory B] :
    TrivialKanFibration ((MonoidalClosed.pre (tailAttachment A).ι).app B) :=
  trivialKanFibration_pre_of_innerAnodyne _ (tailAttachment_innerAnodyne A) B

end SerrePositivity.KST.Fibration
