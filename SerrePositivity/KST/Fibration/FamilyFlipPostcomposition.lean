module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.InternalHomFlipAdjunction

/-! # 元の内部 Hom の添字交換と標的への後合成の可換性 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 元の内部 Hom の交換は、標的の実際の射による後合成を厳密に保つ。 -/
lemma familyFlip_postcomp {K L A B : SSet.{u}} (F : K ⟶ (ihom L).obj A) (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K L B (F ≫ (ihom L).map f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K L A F ≫ (ihom K).map f := by
  change curry ((β_ K L).hom ≫ uncurry (F ≫ (ihom L).map f)) =
    curry ((β_ K L).hom ≫ uncurry F) ≫ (ihom K).map f
  rw [uncurry_natural_right, ← Category.assoc, curry_natural_right]

end SerrePositivity.KST.Fibration
