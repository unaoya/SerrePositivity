module
public import SerrePositivity.KST.Fibration.CoreFactorization
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # 元の押し出しに沿う core 値図式の厳密な貼り合わせ -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.KST.Fibration
open SerrePositivity.InfinityCategories

/-- 元の図式が core を通ることは、押し出しの両成分で同じ図式が core を通ることと同値。 -/
lemma coreFactor_iff_of_isPushout {V E P T C : SSet.{u}}
    {i : V ⟶ E} {j : V ⟶ P} {e : E ⟶ T} {p : P ⟶ T}
    (h : IsPushout i j e p) (f : T ⟶ C) :
    (∃ g : T ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C : SSet.{u}), g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).ι = f) ↔
      (∃ g : E ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C : SSet.{u}), g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).ι = e ≫ f) ∧
      (∃ g : P ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C : SSet.{u}), g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).ι = p ≫ f) := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨⟨e ≫ g, by rw [Category.assoc, hg]⟩,
      ⟨p ≫ g, by rw [Category.assoc, hg]⟩⟩
  · rintro ⟨⟨ge, he⟩, ⟨gp, hp⟩⟩
    have hw : i ≫ ge = j ≫ gp := by
      apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).ι).1
      rw [Category.assoc, he, ← Category.assoc, h.w, Category.assoc, ← hp, ← Category.assoc]
    refine ⟨h.desc ge gp hw, ?_⟩
    apply h.hom_ext
    · rw [← Category.assoc, h.inl_desc, he]
    · rw [← Category.assoc, h.inr_desc, hp]

end SerrePositivity.KST.Fibration
