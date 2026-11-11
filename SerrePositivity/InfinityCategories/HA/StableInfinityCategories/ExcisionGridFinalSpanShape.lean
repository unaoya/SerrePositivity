module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridFinalSpanRetraction
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCornerSpan

/-!
概要：最終面の三点 span と標準有限順序添字の同型。
方針：同じ実図式の native 余錐・頂点・二辺を保持して比較する。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の外側の面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

abbrev ExcisionGridFinalSpanIndex :=
  {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridFullPastIndex.{u} // _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridFinalSpan p}

def excisionGridFinalSpanStandardOrderIso :
    ExcisionGridFinalSpanIndex.{u} ≃o _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCornerSpanIndex.{u} where
  toFun p := ULift.up ⟨(⟨p.val.val.down.val.1.val - 2, by
      have := p.val.val.down.val.1.isLt; omega⟩,
    ⟨p.val.val.down.val.2.val - 2, by have := p.val.val.down.val.2.isLt; omega⟩), by
      have hx := p.property.1
      have hy := p.property.2
      have hp := p.val.property
      change 2 ≤ p.val.val.down.val.1.val at hx
      change 2 ≤ p.val.val.down.val.2.val at hy
      change p.val.val.down.val.1.val + p.val.val.down.val.2.val ≤ 5 at hp
      by_cases hx2 : p.val.val.down.val.1.val = 2
      · left; apply Fin.ext; change _ - 2 = 0; omega
      · right; apply Fin.ext; change _ - 2 = 0; omega⟩
  invFun p := by
    let x := p.down.val.1
    let y := p.down.val.2
    have hx : x.val < 2 := x.isLt
    have hy : y.val < 2 := y.isLt
    have hxy : x.val = 0 ∨ y.val = 0 := p.down.property.imp
      (fun h ↦ congrArg Fin.val h) (fun h ↦ congrArg Fin.val h)
    let a : Fin 4 := ⟨x.val + 2, by omega⟩
    let b : Fin 4 := ⟨y.val + 2, by omega⟩
    let q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} := ULift.up ⟨(a, b), by dsimp [a, b]; omega⟩
    exact ⟨⟨q, by change (x.val + 2) + (y.val + 2) ≤ 5; omega⟩,
      by change 2 ≤ x.val + 2 ∧ 2 ≤ y.val + 2; omega⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply ULift.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · change p.val.val.down.val.1.val - 2 + 2 = p.val.val.down.val.1.val
      have := p.property.1
      change 2 ≤ p.val.val.down.val.1.val at this
      omega
    · change p.val.val.down.val.2.val - 2 + 2 = p.val.val.down.val.2.val
      have := p.property.2
      change 2 ≤ p.val.val.down.val.2.val at this
      omega
  right_inv p := by
    apply ULift.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · change p.down.val.1.val + 2 - 2 = p.down.val.1.val; omega
    · change p.down.val.2.val + 2 - 2 = p.down.val.2.val; omega
  map_rel_iff' := by
    intro a b
    change (a.val.val.down.val.1.val - 2 ≤ b.val.val.down.val.1.val - 2 ∧
      a.val.val.down.val.2.val - 2 ≤ b.val.val.down.val.2.val - 2) ↔ _
    have ha := a.property
    have hb := b.property
    change 2 ≤ a.val.val.down.val.1.val ∧ 2 ≤ a.val.val.down.val.2.val at ha
    change 2 ≤ b.val.val.down.val.1.val ∧ 2 ≤ b.val.val.down.val.2.val at hb
    change _ ↔ (a.val.val.down.val.1.val ≤ b.val.val.down.val.1.val ∧
      a.val.val.down.val.2.val ≤ b.val.val.down.val.2.val)
    omega

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
