module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCenterSpanRetraction
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PastingRightSpanIso

/-!
概要：中央の三点 span と既存の右 span の全単体の順逆写像。
方針：同じ実図式の native 余錐と頂点を保持して比較する。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の中央面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P : Type u} [PartialOrder P]

abbrev ExcisionGridCenterSpanIndex :=
  {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridPastIndex.{u} // _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridCenterSpan p}

def excisionGridCenterSpanToPasting : nerve ExcisionGridCenterSpanIndex.{u} ⟶
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan : SSet.{u}) where
  app n := ↾fun s ↦
    ⟨⟨(stdSimplex.objEquiv.symm (SimplexCategory.mkHom
        ⟨fun k ↦ ⟨(s.obj k).val.val.val.val.down.val.1.val,
            by have := (s.obj k).val.val.property.1; omega⟩,
          fun _ _ h ↦ (s.monotone h).1⟩),
      stdSimplex.objEquiv.symm (SimplexCategory.mkHom
        ⟨fun k ↦ ⟨(s.obj k).val.val.val.val.down.val.2.val - 1,
            by have := (s.obj k).val.val.property.2; omega⟩,
          fun _ _ h ↦ Nat.sub_le_sub_right (s.monotone h).2 1⟩)), by
      intro k hx hy
      have hp := (s.obj k).val.property
      change (s.obj k).val.val.val.val.down.val.1.val +
        (s.obj k).val.val.val.val.down.val.2.val ≤ 3 at hp
      have hx := congrArg Fin.val hx
      have hy := congrArg Fin.val hy
      change (s.obj k).val.val.val.val.down.val.1.val = 2 at hx
      change (s.obj k).val.val.val.val.down.val.2.val - 1 = 1 at hy
      omega⟩, by
      intro k hx
      have hp := (s.obj k).property.1
      change 1 ≤ (s.obj k).val.val.val.val.down.val.1.val at hp
      have hx := congrArg Fin.val hx
      change (s.obj k).val.val.val.val.down.val.1.val = 0 at hx
      omega⟩
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> apply stdSimplex.ext <;> intro k <;> rfl

def excisionGridPastingToCenterSpan : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingRightSpan : SSet.{u}) ⟶
    nerve ExcisionGridCenterSpanIndex.{u} where
  app n := ↾fun s ↦
    (⟨fun k ↦ by
      let x := (stdSimplex.objEquiv s.val.val.1).toOrderHom k
      let y := (stdSimplex.objEquiv s.val.val.2).toOrderHom k
      have hx : x.val < 3 := x.isLt
      have hy : y.val < 2 := y.isLt
      have hx0 : x.val ≠ 0 := fun h ↦ s.property k (Fin.ext h)
      have hcorner := s.val.property k
      have hsum : x.val + (y.val + 1) ≤ 3 := by
        by_cases hx2 : x = 2
        · have hn : y.val ≠ 1 := fun h ↦ hcorner hx2 (Fin.ext h)
          have hxv : x.val = 2 := congrArg Fin.val hx2
          omega
        · have hn : x.val ≠ 2 := fun h ↦ hx2 (Fin.ext h)
          omega
      exact ⟨⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint x ⟨y.val + 1, by omega⟩, hsum⟩,
        by change 1 ≤ x.val ∧ 1 ≤ y.val + 1; omega⟩,
      fun _ _ h ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint_le
        ((stdSimplex.objEquiv s.val.val.1).toOrderHom.monotone h)
        (Nat.add_le_add_right ((stdSimplex.objEquiv s.val.val.2).toOrderHom.monotone h) 1)⟩ :
      Fin (n.unop.len + 1) →o ExcisionGridCenterSpanIndex.{u}).toFunctor
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    · intro i j f; apply Subsingleton.elim
    · intro i; rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
