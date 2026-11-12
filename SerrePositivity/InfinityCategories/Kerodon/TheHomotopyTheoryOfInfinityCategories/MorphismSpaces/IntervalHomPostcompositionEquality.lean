module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostcompositionLaws
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalHomFamilyProjection

/-!
概要：同じ合成を持つ二つの後合成は、端点を正規化した同じ Hom 作用を与える。
方針：元の二つの作用の合成公式と、合成した射の等式を使う。
規約：中間の端点表示が異なっても、元の同じ端点を保持する。
使われ方：比較三角形の共有頂点への Hom 射影の厳密な一致。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 元の合成が等しければ、中間の端点表示に依らず同じ正規化 Hom の合成作用となる。 -/
lemma intervalMappingPostOfEq_comp_congr {X Y Z : SSet.{u}}
    (f f' : X ⟶ Y) (g g' : Y ⟶ Z) (x y : X _⦋0⦌)
    {x₁ y₁ x₁' y₁' : Y _⦋0⦌} {x₂ y₂ : Z _⦋0⦌}
    (hfx : f.app _ x = x₁) (hfy : f.app _ y = y₁)
    (hfx' : f'.app _ x = x₁') (hfy' : f'.app _ y = y₁')
    (hgx : g.app _ x₁ = x₂) (hgy : g.app _ y₁ = y₂)
    (hgx' : g'.app _ x₁' = x₂) (hgy' : g'.app _ y₁' = y₂)
    (h : f ≫ g = f' ≫ g') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq f x y hfx hfy ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq g x₁ y₁ hgx hgy =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq f' x y hfx' hfy' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq g' x₁' y₁' hgx' hgy' := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_uncurry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_universal_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_universal_uncurry,
    Category.assoc, Category.assoc, h]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
