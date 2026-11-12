module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SimplexDiagonalContraction

/-!
概要：反対単体圏の対角の comma の収縮を二つの自然変換で結ぶ。
方針：後続部分の包含と新しい零頂点を使い、全射について自然性を示す。
規約：元の二つの指定次数を保持する。
使われ方：対角の comma の弱可縮性と sifted 性の判定。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：最小頂点を追加した comma 対象から元の対象への自然変換。
方針：元の単体を後続部分へ入れる作用素を反転する。
規約：元の二つの comma の射を厳密に回収する。
使われ方：恒等関手への収縮。 -/
def simplexDiagonalPrefixToId (m n : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallSimplexOpposite.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexDiagonalPrefix m n ⟶ 𝟭 _ where
  app a := StructuredArrow.homMk
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixTail a.right.objDown.down.unop).op) (by
      apply Prod.ext
      · change ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixTail a.right.objDown.down.unop ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixCone a.hom.1.down.unop).op) = _
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixTail_comp_cone]
        rfl
      · change ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixTail a.right.objDown.down.unop ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixCone a.hom.2.down.unop).op) = _
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixTail_comp_cone]
        rfl)
  naturality {a b} f := by
    apply StructuredArrow.hom_ext
    change ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixTail b.right.objDown.down.unop ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixMap f.right.down.unop).op) =
        ULift.up ((f.right.down.unop ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixTail a.right.objDown.down.unop).op)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixTail_naturality]

/-- 概要：最小頂点を追加した対象から零次数の最小対象への自然変換。
方針：新しい零頂点への制限を使い、全作用素が零を保つことを適用する。
規約：定値先は元の指定した零次数対象。
使われ方：定値関手への収縮。 -/
def simplexDiagonalPrefixToZero (m n : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallSimplexOpposite.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexDiagonalPrefix m n ⟶ (Functor.const _).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexDiagonalZero m n) where
  app a := StructuredArrow.homMk
    (ULift.up (SimplexCategory.const ⦋0⦌ ⦋a.right.objDown.down.unop.len + 1⦌ 0).op) (by
      apply Prod.ext
      · change ULift.up ((SimplexCategory.const ⦋0⦌ _ 0 ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixCone a.hom.1.down.unop).op) = _
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixCone_zero]
        rfl
      · change ULift.up ((SimplexCategory.const ⦋0⦌ _ 0 ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixCone a.hom.2.down.unop).op) = _
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixCone_zero]
        rfl)
  naturality {a b} f := by
    apply StructuredArrow.hom_ext
    change ULift.up ((SimplexCategory.const ⦋0⦌ _ 0 ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixMap f.right.down.unop).op) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexPrefixMap_zero]
    rfl

/-- 概要：反対単体圏の二項対角の元の各 comma の nerve は弱可縮。
方針：構成した共通の収縮関手と二つの自然変換を Kan 標的で反転する。
規約：comma に始対象があるとは仮定しない。
使われ方：幾何学的実現の添字の sifted 性。 -/
lemma simplexDiagonalComma_isWeaklyContractible (m n : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallSimplexOpposite.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (nerve (StructuredArrow (m, n) _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexDegreeDiagonal)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.nerve_isWeaklyContractible_of_contractionSpan (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexDiagonalZero m n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplexDiagonalPrefix m n) (simplexDiagonalPrefixToId m n)
    (simplexDiagonalPrefixToZero m n)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
