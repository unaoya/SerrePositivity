module
public import SerrePositivity.KST.Fibration.InitialHornPoint
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.InnerAnodyneEquivalence

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
def tailAttachment (A : SSet.{u}) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[1] : SSet.{u})).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (⊥ : A.Subcomplex) (horn 1 0)

/-- 貼り合わせから元の全 join への包含は inner anodyne。 -/
lemma tailAttachment_innerAnodyne (A : SSet.{u}) :
    innerAnodyneExtensions (tailAttachment A).ι :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_innerAnodyne_of_leftAnodyne _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_horn 0 (by decide))

/-- 最後の元の辺を貼り合わせに含める。 -/
def tailAttachmentEdge (A : SSet.{u}) : (Δ[1] : SSet.{u}) ⟶ (tailAttachment A : SSet.{u}) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso A (Δ[1] : SSet.{u})).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionLeft (⊥ : A.Subcomplex) (horn 1 0)

/-- 元の先行錐を貼り合わせに含める。 -/
def tailAttachmentPrefix (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Λ[1, 0] : SSet.{u}) ⟶ (tailAttachment A : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnionRight (⊥ : A.Subcomplex) (horn 1 0)

/-- 貼り合わせの普遍性は、元の共有始点と二つの包含で与えられる。 -/
theorem tailAttachment_isPushout (A : SSet.{u}) :
    IsPushout (horn 1 0).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A (Λ[1, 0] : SSet.{u}))
      (tailAttachmentEdge A) (tailAttachmentPrefix A) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion_isPushout (⊥ : A.Subcomplex) (horn 1 0)).of_iso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso A (Λ[1, 0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso A (Δ[1] : SSet.{u}))
    (Iso.refl _) (Iso.refl _)
  · apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso A (Λ[1, 0] : SSet.{u})).inv).1
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (horn 1 0).ι ≫ _ = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc]
    simp [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso]
  · apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso A (Λ[1, 0] : SSet.{u})).inv).1
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (⊥ : A.Subcomplex).ι (𝟙 _) ≫ 𝟙 _) = _
    rw [Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
    simp [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso]
  · change _ ≫ 𝟙 _ = _ ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.emptyJoinIso A (Δ[1] : SSet.{u})).inv ≫ _)
    simp only [Category.comp_id, Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl

/-- 元の全図式から貼り合わせへの制限は全境界持ち上げを持つ。 -/
lemma tailAttachment_pre_trivialKanFibration (A B : SSet.{u}) [Quasicategory B] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((MonoidalClosed.pre (tailAttachment A).ι).app B) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne _ (tailAttachment_innerAnodyne A) B

end SerrePositivity.KST.Fibration
