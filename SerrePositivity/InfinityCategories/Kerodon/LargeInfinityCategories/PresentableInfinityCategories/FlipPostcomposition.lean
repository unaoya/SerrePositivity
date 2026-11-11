module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.InternalHomFlipAdjunction

/-!
概要：関手族の変数交換と標的への後合成を照合する。
方針：uncurry の後合成自然性を使う。
規約：全単体の厳密な等式である。
使われ方：有限余積の全余錐族の像を同じ底図式へ置く。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：全関手族の変数交換は標的の後合成と可換。
方針：二つの curry を uncurry の自然性で比較する。
規約：元の全族を保持する。
使われ方：余錐族の像の底図式の同定。 -/
lemma flip_postcomposition {A B X Y : SSet.{u}} (f : A ⟶ (ihom B).obj X) (q : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A B Y (f ≫ (ihom B).map q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A B X f ≫ (ihom A).map q := by
  change curry ((β_ A B).hom ≫ uncurry (f ≫ (ihom B).map q)) =
    curry ((β_ A B).hom ≫ uncurry f) ≫ (ihom A).map q
  rw [uncurry_natural_right, ← curry_natural_right, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
