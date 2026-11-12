module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid

/-!
概要：任意の四角形を厳密に保つ比較格子と二段階の局所余極限を構成する。
方針：有限順序添字の厳密左 Kan 拡張と、指定終対象への延長を交互に使う。
規約：各面の押し出し性はまだ結論しない。使われ方：HA 1.4.2.15 の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
def excisionGridFirstNewZero : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridMiddleIndex.{u} :=
  ⟨ULift.up ⟨(3, 1), by decide⟩, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
def excisionGridSecondNewZero : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridMiddleIndex.{u} :=
  ⟨ULift.up ⟨(1, 3), by decide⟩, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
lemma ExcisionGridExtension.first_new_zero {X : SSet.{u}}
    {G : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridExtension G z) :
    d.full.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex excisionGridFirstNewZero.val) = z :=
  d.zero_full (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex excisionGridFirstNewZero)
    (by change ¬ ((3 : ℕ) ≤ 2 ∧ (1 : ℕ) ≤ 2); decide)

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
lemma ExcisionGridExtension.second_new_zero {X : SSet.{u}}
    {G : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} ⟶ X} {z : X _⦋0⦌}
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridExtension G z) :
    d.full.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex excisionGridSecondNewZero.val) = z :=
  d.zero_full (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex excisionGridSecondNewZero)
    (by change ¬ ((1 : ℕ) ≤ 2 ∧ (3 : ℕ) ≤ 2); decide)

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
lemma ExcisionSquareGrid.zero_seed_full {X : SSet.{u}}
    {R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} {z : X _⦋0⦌} (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid R z)
    (v : (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u}) _⦋0⦌)
    (hv : ¬ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridSquare (nerveEquiv v)) :
    d.extension.full.app (Opposite.op ⦋0⦌)
      ((nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSeedInclusion ≫ nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCoreInclusion ≫
        nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridMiddleInclusion).app (Opposite.op ⦋0⦌) v) = z := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app d.extension.seed_restriction (Opposite.op ⦋0⦌)) v
  exact h.trans (d.zero_seed v hv)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
