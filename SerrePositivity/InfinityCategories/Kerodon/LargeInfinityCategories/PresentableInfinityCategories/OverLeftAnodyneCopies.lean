module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.OverCellCopies
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory

/-!
概要：底上のセルの全コピーを忘却した射の左アノダイン性。
方針：底上の余積余錐を忘却し、元の左アノダイン射の余積として判定する。
規約：底上の射そのものの全空間の射を扱い、底の充填性を仮定しない。
使われ方：連続 left fibration 置換の単位の左アノダイン性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 底上の左アノダインな射の余積も、全空間で左アノダインである。 -/
instance over_leftAnodyne_isStableUnderCoproducts (B : SSet.{u}) (J : Type u) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.inverseImage (Over.forget B)).IsStableUnderColimitsOfShape
      (Discrete J) where
  condition D E c d hc hd f hf φ hφ := by
    exact MorphismProperty.IsStableUnderColimitsOfShape.condition
      (W := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions)
      (D ⋙ Over.forget B) (E ⋙ Over.forget B)
      ((Over.forget B).mapCocone c) ((Over.forget B).mapCocone d)
      (isColimitOfPreserves (Over.forget B) hc)
      (isColimitOfPreserves (Over.forget B) hd)
      (Functor.whiskerRight f (Over.forget B)) hf φ.left
      (fun j ↦ congrArg (fun k ↦ k.left) (hφ j))

/-- 同じ底上の左アノダインなセルの全コピーは、全空間で左アノダイン。 -/
lemma overCellCopiesMap_leftAnodyne {B : SSet.{u}} (A : Over B) {D E : Over B}
    (i : D ⟶ E) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i.left) (X : Over B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.overCellCopiesMap A i).app X).left := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.inverseImage (Over.forget B))
    (colimMap (Discrete.natTrans
      (F := Discrete.functor (fun _ : A ⟶ X ↦ D))
      (G := Discrete.functor (fun _ : A ⟶ X ↦ E)) (fun _ ↦ i)))
  exact MorphismProperty.colimMap _ (fun _ ↦ hi)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
