module
public import SerrePositivity.KST.SConstruction.PointwiseCofiberFamilies

/-! # 関手圏の指定された辺の cofiber
概要：安定な標的の関手圏では各辺が cofiber 正方形を持つ。
方針：cofiber 射影の切断を転置し、入力の辺を厳密に回収する。
規約：パラメーターは任意の単体集合。使われ方：反復 S• の安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：転置した cofiber の族の下辺は入力の族の転置。
方針：内部 Hom の制限と転置の自然性を用いる。
規約：標的の安定性は不要。使われ方：cofiber の境界を指定する。 -/
lemma cofiberFamilySquare_bottomEdge {A C : SSet.{u}} (H : A ⟶ cofiberDiagrams C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ cofiberFamilySquare H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A (Δ[1] : SSet.{u}) C (H ≫ cofiberProjection C) := by
  rw [cofiberFamilySquare, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app]
  rfl

/-- 概要：関手圏の指定された辺は cofiber 正方形を持つ。
方針：転置した辺を cofiber 射影の切断で持ち上げ、再び転置する。
規約：入力の辺は厳密な等号で保持する。使われ方：関手圏の安定性。 -/
lemma functor_cofiberSquare_nonempty {A C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    {x y : ((ihom A).obj C) _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj C)) x y) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f) := by
  let d : (Δ[1] : SSet.{u}) ⟶ (ihom A).obj C := SSet.yonedaEquiv.symm f.edge
  let h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[1] : SSet.{u}) A C d
  let H := h ≫ cofiberSection C
  refine ⟨{
    square := cofiberFamilySquare H
    zero_corner := cofiberFamilySquare_zero_corner H
    bottom_edge := ?_
    isPushout := cofiberFamilyTriangle_isCofiber H }⟩
  rw [cofiberFamilySquare_bottomEdge]
  have he : H ≫ cofiberProjection C = h := by
    dsimp only [H]
    rw [Category.assoc, cofiberSection_projection, Category.comp_id]
  rw [he]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[1] : SSet.{u}) A C).symm_apply_apply d

end SerrePositivity.KST.SConstruction
