module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCenterSpanShapeIso

/-!
概要：三点 span の標準有限順序添字とホーンの厳密同型。
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

abbrev ExcisionCornerSpanIndex := ULift.{u} {p : Fin 2 × Fin 2 // p.1 = 0 ∨ p.2 = 0}

def excisionGridCenterSpanStandardOrderIso :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCenterSpanIndex.{u} ≃o ExcisionCornerSpanIndex.{u} where
  toFun p := ULift.up ⟨(⟨p.val.val.val.val.down.val.1.val - 1, by
      have := p.val.val.property.1; omega⟩,
    ⟨p.val.val.val.val.down.val.2.val - 1, by have := p.val.val.property.2; omega⟩), by
      have hx := p.property.1
      have hy := p.property.2
      have hp := p.val.property
      change 1 ≤ p.val.val.val.val.down.val.1.val at hx
      change 1 ≤ p.val.val.val.val.down.val.2.val at hy
      change p.val.val.val.val.down.val.1.val + p.val.val.val.val.down.val.2.val ≤ 3 at hp
      by_cases hx1 : p.val.val.val.val.down.val.1.val = 1
      · left; apply Fin.ext; change _ - 1 = 0; omega
      · right; apply Fin.ext; change _ - 1 = 0; omega⟩
  invFun p := by
    let x := p.down.val.1
    let y := p.down.val.2
    have hx : x.val < 2 := x.isLt
    have hy : y.val < 2 := y.isLt
    have hxy : x.val = 0 ∨ y.val = 0 := p.down.property.imp
      (fun h ↦ congrArg Fin.val h) (fun h ↦ congrArg Fin.val h)
    exact ⟨⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint x.succ y.succ, by
      change (x.val + 1) + (y.val + 1) ≤ 3; omega⟩,
      by change 1 ≤ x.val + 1 ∧ 1 ≤ y.val + 1; omega⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply ULift.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · change p.val.val.val.val.down.val.1.val - 1 + 1 = p.val.val.val.val.down.val.1.val
      have := p.property.1
      change 1 ≤ p.val.val.val.val.down.val.1.val at this
      omega
    · change p.val.val.val.val.down.val.2.val - 1 + 1 = p.val.val.val.val.down.val.2.val
      have := p.property.2
      change 1 ≤ p.val.val.val.val.down.val.2.val at this
      omega
  right_inv p := by
    apply ULift.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · change p.down.val.1.val + 1 - 1 = p.down.val.1.val; omega
    · change p.down.val.2.val + 1 - 1 = p.down.val.2.val; omega
  map_rel_iff' := by
    intro a b
    change (a.val.val.val.val.down.val.1.val - 1 ≤ b.val.val.val.val.down.val.1.val - 1 ∧
      a.val.val.val.val.down.val.2.val - 1 ≤ b.val.val.val.val.down.val.2.val - 1) ↔ _
    have ha := a.property
    have hb := b.property
    change 1 ≤ a.val.val.val.val.down.val.1.val ∧ 1 ≤ a.val.val.val.val.down.val.2.val at ha
    change 1 ≤ b.val.val.val.val.down.val.1.val ∧ 1 ≤ b.val.val.val.val.down.val.2.val at hb
    change _ ↔ (a.val.val.val.val.down.val.1.val ≤ b.val.val.val.val.down.val.1.val ∧
      a.val.val.val.val.down.val.2.val ≤ b.val.val.val.val.down.val.2.val)
    omega

def excisionCornerSpanNerveIso : nerve ExcisionCornerSpanIndex.{u} ≅
    (horn 2 0 : SSet.{u}) :=
  PartOrd.nerveFunctor.mapIso (PartOrd.Iso.mk
    (α := PartOrd.of ExcisionCornerSpanIndex.{u})
    (β := PartOrd.of _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCenterSpanIndex.{u})
    excisionGridCenterSpanStandardOrderIso.symm) ≪≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCenterSpanPastingIso ≪≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpanIso.symm

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
