module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PosetMaximalSubtypePushout
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.PosetLowerJoinIso

/-!
概要：極大点の追加を、厳密下方 nerve の終点余錐との元の包含による pushout にする。
方針：弱下方 nerve の元の余錐表示を部分型 pushout へ接続する。
規約：除去部分・厳密下方部分・元の全 nerve の包含を保持する。
使われ方：固定下方部分を保つ実余錐の帰納拡張。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：元の極大点追加は厳密下方部分の終点余錐との pushout。
方針：元の下方余錐の同型。規約：元の全包含。使われ方：厳密余錐持ち上げ。 -/
lemma posetNerve_maximal_cone_isPushout {P : Type u} [PartialOrder P]
    (a : P) (ha : IsMax a) :
    IsPushout
      (nerveMap (⟨fun p ↦ ⟨p.val, p.property.ne⟩, fun _ _ h ↦ h⟩ :
        {p : P // p < a} →o {p : P // p ≠ a}).toFunctor)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (nerve {p : P // p < a}) (Δ[0] : SSet.{u}))
      (nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion (fun p : P ↦ p ≠ a)))
      ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.posetLowerJoinIso a).hom ≫
        nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion (fun p : P ↦ p ≤ a))) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.posetNerve_maximal_subtype_isPushout a ha).of_iso'
    (Iso.refl _) (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.posetLowerJoinIso a) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simpa only [Iso.refl_hom, Category.id_comp] using (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.posetLowerJoinIso_inl a).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
