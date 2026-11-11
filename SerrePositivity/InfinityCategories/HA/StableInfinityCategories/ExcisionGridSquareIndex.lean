module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex

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
def IsExcisionGridSquare (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u}) : Prop :=
  p.val.val.val.down.val.1.val ≤ 1 ∧ p.val.val.val.down.val.2.val ≤ 1

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
abbrev ExcisionGridSquareIndex := {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} // IsExcisionGridSquare p}

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
lemma excisionGridSquare_downward {a b : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u}} (h : a ≤ b)
    (hb : IsExcisionGridSquare b) : IsExcisionGridSquare a :=
  ⟨Nat.le_trans h.1 hb.1, Nat.le_trans h.2 hb.2⟩

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
def excisionGridSquarePoint (i j : Fin 2) : ExcisionGridSquareIndex.{u} := by
  let x : Fin 4 := ⟨i.val, by omega⟩
  let y : Fin 4 := ⟨j.val, by omega⟩
  let p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} := ULift.up ⟨(x, y), by dsimp [x, y]; omega⟩
  have hp : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridCore p := by dsimp [p, x, y, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridCore]; omega
  let m : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridMiddleIndex.{u} := ⟨p, Or.inl hp⟩
  let c : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} := ⟨m, hp⟩
  have hc : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridSeed c := by dsimp [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridSeed, c, m, p, x, y]; omega
  let s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSeedIndex.{u} := ⟨c, hc⟩
  exact ⟨s, by dsimp [IsExcisionGridSquare, s, c, m, p, x, y]; omega⟩

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
def excisionGridSquareOrderIso : ExcisionGridSquareIndex.{u} ≃o
    ULift.{u} (Fin 2) × ULift.{u} (Fin 2) where
  toFun p :=
    (ULift.up ⟨p.val.val.val.val.down.val.2.val, Nat.lt_succ_of_le p.property.2⟩,
      ULift.up ⟨p.val.val.val.val.down.val.1.val, Nat.lt_succ_of_le p.property.1⟩)
  invFun p := excisionGridSquarePoint p.2.down p.1.down
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply ULift.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> rfl
  right_inv p := by
    apply Prod.ext <;> apply ULift.ext <;> apply Fin.ext <;> rfl
  map_rel_iff' := by
    intro a b
    exact and_comm

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
