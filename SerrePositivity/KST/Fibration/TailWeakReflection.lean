module
public import SerrePositivity.KST.Fibration.TailWeakModel
public import SerrePositivity.KST.Fibration.CoreFactorPushout
public import SerrePositivity.KST.Fibration.InnerAnodyneCoreReflection
public import SerrePositivity.KST.Fibration.WeakStringsSimplicial

/-! # 先行列と最後の W 辺から元の全合成辺の W 条件を反映する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 貼り合わせ上の両 W 条件は、商の元の実図式の core への厳密因子分解と同値。 -/
lemma tailWeakPredicate_functorVertex_iff_factorCore {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ)
    (F : (tailAttachment (Δ[n] : SSet.{u}) : SSet.{u}) ⟶ B.obj) :
    (tailWeakPredicate q n).predicate (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) ↔
      ∃ g : (tailAttachment (Δ[n] : SSet.{u}) : SSet.{u}) ⟶
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj : SSet.{u}),
        g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C.obj).ι = F ≫ q.hom := by
  rw [tailWeakPredicate_iff]
  change weakStringPredicate q ⦋n + 1⦌ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (standardTailPrefix n ≫ F)) ∧
    weakArrowPredicate q (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (tailAttachmentEdge (Δ[n] : SSet.{u}) ≫ F)) ↔ _
  rw [← weakStringPredicate_one_iff, weakStringPredicate_functorVertex_iff_factorCore,
    weakStringPredicate_functorVertex_iff_factorCore]
  have h := coreFactor_iff_of_isPushout (standardTail_isPushout n) (F ≫ q.hom)
  constructor
  · rintro ⟨hp, he⟩
    apply h.2
    exact ⟨by simpa only [Category.assoc] using he,
      by simpa only [Category.assoc] using hp⟩
  · intro hf
    obtain ⟨he, hp⟩ := h.1 hf
    exact ⟨by simpa only [Category.assoc] using hp,
      by simpa only [Category.assoc] using he⟩

/-- 元の長い W 列の全辺条件は、貼り合わせに制限した先行列と最後の辺から正確に反映される。 -/
theorem weakStringPredicate_iff_tail {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ)
    (v : ((ihom (Δ[n + 2] : SSet.{u})).obj B.obj) _⦋0⦌) :
    weakStringPredicate q ⦋n + 2⦌ v ↔ (tailWeakPredicate q n).predicate
      (((pre (standardTailInclusion n)).app B.obj).app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨F, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[n + 2] : SSet.{u}) B.obj).surjective v
  change weakStringPredicate q ⦋n + 2⦌ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) ↔
    (tailWeakPredicate q n).predicate (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (standardTailInclusion n ≫ F))
  rw [weakStringPredicate_functorVertex_iff_factorCore,
    tailWeakPredicate_functorVertex_iff_factorCore]
  constructor
  · rintro ⟨G, hG⟩
    exact ⟨standardTailInclusion n ≫ G, by rw [Category.assoc, hG, ← Category.assoc]⟩
  · intro h
    apply coreFactor_of_innerAnodyne ⦋n + 2⦌ (standardTailInclusion n)
      (standardTailInclusion_innerAnodyne n) (F ≫ q.hom)
    simpa only [Category.assoc] using h

end SerrePositivity.KST.Fibration
