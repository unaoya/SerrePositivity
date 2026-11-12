module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopConeZeroCornerForget

/-!
概要：元の普遍 loop 錐の指定点の始対象性と、同じ零隅四角形への移送。
方針：固定 cospan の終対象の自己比較と、実 classifier・選択忘却を接続する。
規約：最後の全四角形図式を厳密に保つ。使われ方：同じ loop 四角形の押し出し性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma zeroCornerSquareConeIso_inv_diagram (X : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareConeIso X).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroCornerSquareVertex).ι =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (horn 2 2 : SSet.{u}) X)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterCospanVertex).ι ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareConeFunctorIso X).inv := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareConeFunctorIso X).hom).1
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareConeIso X).inv ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroCornerSquareVertex).ι ≫
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareConeFunctorIso X).hom) := Category.assoc _ _ _
    _ = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareConeIso X).inv ≫
        ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareConeIso X).hom ≫ pullback.fst _ _) :=
      congrArg (fun f ↦ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareConeIso X).inv ≫ f)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareConeIso_diagram X).symm
    _ = pullback.fst _ _ := by
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = _ := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 元の普遍 loop 錐の同じ指定点と四角形を保つ比較。 -/
lemma loopConeZeroCornerForget_diagram (X : SSet.{u}) [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeZeroCornerForget X ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroCornerSquareVertex).ι =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeObjectDiagram X ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareConeFunctorIso X).inv := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeZeroCornerForget]
  simp only [Category.assoc, zeroCornerSquareConeIso_inv_diagram,
    reassoc_of% _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coneChoiceForget_diagram, reassoc_of% _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopConeChoiceIso_diagram]
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
