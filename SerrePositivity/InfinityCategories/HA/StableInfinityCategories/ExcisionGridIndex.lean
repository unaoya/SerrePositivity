module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeNerve

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
abbrev ExcisionGridIndex := ULift.{u} {p : Fin 4 × Fin 4 //
  p.1.val ≤ p.2.val + 2 ∧ p.2.val ≤ p.1.val + 2}

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
def IsExcisionGridCore (p : ExcisionGridIndex.{u}) : Prop :=
  p.down.val.1.val ≤ 2 ∧ p.down.val.2.val ≤ 2

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
def IsExcisionGridMiddle (p : ExcisionGridIndex.{u}) : Prop :=
  IsExcisionGridCore p ∨ (p.down.val.1.val = 3 ∧ p.down.val.2.val = 1) ∨
    (p.down.val.1.val = 1 ∧ p.down.val.2.val = 3)

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
abbrev ExcisionGridMiddleIndex := {p : ExcisionGridIndex.{u} // IsExcisionGridMiddle p}

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
abbrev ExcisionGridCoreIndex :=
  {p : ExcisionGridMiddleIndex.{u} // IsExcisionGridCore p.val}

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
def IsExcisionGridSeed (p : ExcisionGridCoreIndex.{u}) : Prop :=
  p.val.val.down.val.1.val + p.val.val.down.val.2.val ≤ 2

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
abbrev ExcisionGridSeedIndex := {p : ExcisionGridCoreIndex.{u} // IsExcisionGridSeed p}

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
lemma excisionGridCore_downward {a b : ExcisionGridIndex.{u}} (h : a ≤ b)
    (hb : IsExcisionGridCore b) : IsExcisionGridCore a := by
  exact ⟨Nat.le_trans h.1 hb.1, Nat.le_trans h.2 hb.2⟩

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
lemma excisionGridMiddle_downward {a b : ExcisionGridIndex.{u}} (h : a ≤ b)
    (hb : IsExcisionGridMiddle b) : IsExcisionGridMiddle a := by
  rcases hb with hb | hb | hb
  · exact Or.inl (excisionGridCore_downward h hb)
  · have ha := a.down.property
    have hab₁ := h.1
    have hab₂ := h.2
    dsimp only [IsExcisionGridMiddle, IsExcisionGridCore]
    change a.down.val.1.val ≤ b.down.val.1.val at hab₁
    change a.down.val.2.val ≤ b.down.val.2.val at hab₂
    omega
  · have ha := a.down.property
    have hab₁ := h.1
    have hab₂ := h.2
    dsimp only [IsExcisionGridMiddle, IsExcisionGridCore]
    change a.down.val.1.val ≤ b.down.val.1.val at hab₁
    change a.down.val.2.val ≤ b.down.val.2.val at hab₂
    omega

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
lemma excisionGridSeed_downward {a b : ExcisionGridCoreIndex.{u}} (h : a ≤ b)
    (hb : IsExcisionGridSeed b) : IsExcisionGridSeed a := by
  dsimp only [IsExcisionGridSeed] at hb ⊢
  exact (Nat.add_le_add h.1 h.2).trans hb

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
abbrev excisionGridSeedInclusion : ExcisionGridSeedIndex.{u} ⥤ ExcisionGridCoreIndex.{u} :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion IsExcisionGridSeed

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
abbrev excisionGridCoreInclusion : ExcisionGridCoreIndex.{u} ⥤ ExcisionGridMiddleIndex.{u} :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion (fun p : ExcisionGridMiddleIndex.{u} ↦ IsExcisionGridCore p.val)

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
abbrev excisionGridMiddleInclusion : ExcisionGridMiddleIndex.{u} ⥤ ExcisionGridIndex.{u} :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion IsExcisionGridMiddle

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
