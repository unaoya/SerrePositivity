module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostIso

/-!
概要：端点を正規化した区間写像空間の後合成は、元の射の合成と厳密に可換。
方針：普遍的な区間族へ展開し、元の二つの後合成の結合則を使う。
規約：全ての端点表示の等式を含め、全パラメーターでの射を照合する。
使われ方：同じ Yoneda 後合成と、指定点評価に沿う後合成を一つにまとめる。

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

/-- 端点を正規化した二つの区間後合成は、合成した元の射の同じ後合成に等しい。 -/
lemma intervalMappingPostOfEq_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x y : X _⦋0⦌) (x' y' : Y _⦋0⦌) (x'' y'' : Z _⦋0⦌)
    (hx : f.app _ x = x') (hy : f.app _ y = y')
    (hx' : g.app _ x' = x'') (hy' : g.app _ y' = y'') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq f x y hx hy ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq g x' y' hx' hy' =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq (f ≫ g) x y
      ((congrArg (g.app (Opposite.op ⦋0⦌)) hx).trans hx')
      ((congrArg (g.app (Opposite.op ⦋0⦌)) hy).trans hy') := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_uncurry]
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_uncurry f x y hx hy (𝟙 _)
  have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_uncurry (f ≫ g) x y
    ((congrArg (g.app (Opposite.op ⦋0⦌)) hx).trans hx')
    ((congrArg (g.app (Opposite.op ⦋0⦌)) hy).trans hy') (𝟙 _)
  simp only [Category.id_comp] at h₁ h₂
  rw [h₁, h₂, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
