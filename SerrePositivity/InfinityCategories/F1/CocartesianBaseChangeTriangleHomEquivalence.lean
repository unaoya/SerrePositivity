module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeTriangleHom
public import SerrePositivity.InfinityCategories.F1.EquivalenceTriangleFaceEquivalence
public import SerrePositivity.InfinityCategories.F1.IntervalMappingPostEquivalence

/-!
概要：元の比較三角形の Hom から、元の直接の比較 path の Hom への射影は同値。
方針：同じ長辺への制限の充満忠実性を、端点固定の元の区間 Hom に移す。
規約：元の Hom 比較作用を厳密に回収する同じ射影そのもの。
使われ方：元の底変換比較 span の合成とセル制限の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 同じ元の比較三角形の Hom の長辺への射影は同値。 -/
lemma cocartesianBaseChangeTriangleHomLong_isQCatEquivalence
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
    (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C)) :
    IsQCatEquivalence (cocartesianBaseChangeTriangleHomLong l k p q) := by
  unfold cocartesianBaseChangeTriangleHomLong
  exact (equivalenceTriangleFace_isQCatEquivalence _ 1).isFullyFaithful
    |>.intervalMappingPostOfEq_isQCatEquivalence _ _ _ _

end SerrePositivity.InfinityCategories
