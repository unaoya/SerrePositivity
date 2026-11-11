module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridLowerRectangle
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerCocone

/-!
概要：格子の (2,1) における下方添字と五頂点角の厳密同型。
方針：元の射影・実余錐・全単体の頂点式を保持して比較する。
規約：一般安定性の結論は先取りしない。使われ方：HA 1.4.2.15 の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
variable {P : Type u} [PartialOrder P]

abbrev ExcisionGridLowerSeed :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeLowerIndex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridSeed (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint.{u} 2 1)

def excisionGridLowerSeedToCorner : nerve ExcisionGridLowerSeed.{u} ⟶
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) where
  app n := ↾fun s ↦
    ⟨(stdSimplex.objEquiv.symm (SimplexCategory.mkHom
        ⟨fun k ↦ ⟨(s.obj k).val.val.val.down.val.1.val,
            by have := (s.obj k).val.property.1; omega⟩,
          fun _ _ h ↦ (s.monotone h).1⟩),
      stdSimplex.objEquiv.symm (SimplexCategory.mkHom
        ⟨fun k ↦ ⟨(s.obj k).val.val.val.down.val.2.val,
            by have := (s.obj k).property.2.2; change _ ≤ 1 at this; omega⟩,
          fun _ _ h ↦ (s.monotone h).2⟩)), by
      intro k hx hy
      have hp := (s.obj k).property.1
      change (s.obj k).val.val.val.down.val.1.val +
        (s.obj k).val.val.val.down.val.2.val ≤ 2 at hp
      have hx := congrArg Fin.val hx
      have hy := congrArg Fin.val hy
      change (s.obj k).val.val.val.down.val.1.val = 2 at hx
      change (s.obj k).val.val.val.down.val.2.val = 1 at hy
      omega⟩
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply Prod.ext <;> apply stdSimplex.ext <;> intro k <;> rfl

def excisionGridCornerToLowerSeed : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) ⟶
    nerve ExcisionGridLowerSeed.{u} where
  app n := ↾fun s ↦
    (⟨fun k ↦ ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint ((stdSimplex.objEquiv s.val.1).toOrderHom k)
        (((stdSimplex.objEquiv s.val.2).toOrderHom k).castSucc), by
          constructor
          · have h := s.property k
            have hx := ((stdSimplex.objEquiv s.val.1).toOrderHom k).isLt
            have hy := ((stdSimplex.objEquiv s.val.2).toOrderHom k).isLt
            change _ < 3 at hx
            change _ < 2 at hy
            dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridSeed, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint]
            by_cases hx' : (stdSimplex.objEquiv s.val.1).toOrderHom k = 2
            · have := h hx'
              have hn : ((stdSimplex.objEquiv s.val.2).toOrderHom k).val ≠ 1 := by
                intro hn; exact this (Fin.ext hn)
              have hxv := congrArg Fin.val hx'
              change ((stdSimplex.objEquiv s.val.1).toOrderHom k).val +
                ((stdSimplex.objEquiv s.val.2).toOrderHom k).val ≤ 2
              change ((stdSimplex.objEquiv s.val.1).toOrderHom k).val = 2 at hxv
              omega
            · have hxn : ((stdSimplex.objEquiv s.val.1).toOrderHom k).val ≠ 2 := by
                intro hn; exact hx' (Fin.ext hn)
              change ((stdSimplex.objEquiv s.val.1).toOrderHom k).val +
                ((stdSimplex.objEquiv s.val.2).toOrderHom k).val ≤ 2
              omega
          · constructor
            · change ((stdSimplex.objEquiv s.val.1).toOrderHom k).val ≤ 2
              exact Nat.le_of_lt_succ ((stdSimplex.objEquiv s.val.1).toOrderHom k).isLt
            · change ((stdSimplex.objEquiv s.val.2).toOrderHom k).val ≤ 1
              exact Nat.le_of_lt_succ ((stdSimplex.objEquiv s.val.2).toOrderHom k).isLt⟩,
      fun _ _ h ↦ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint_le
        ((stdSimplex.objEquiv s.val.1).toOrderHom.monotone h)
        ((stdSimplex.objEquiv s.val.2).toOrderHom.monotone h)⟩ :
      Fin (n.unop.len + 1) →o ExcisionGridLowerSeed.{u}).toFunctor
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    · intro i j f; apply Subsingleton.elim
    · intro i; rfl

def excisionGridLowerSeedCornerIso : nerve ExcisionGridLowerSeed.{u} ≅
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) where
  hom := excisionGridLowerSeedToCorner
  inv := excisionGridCornerToLowerSeed
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.nerve.ext_of_isThin
    funext k
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply ULift.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply Prod.ext <;> apply stdSimplex.ext <;> intro k <;> rfl

lemma excisionGridLowerSeedCornerIso_projection :
    excisionGridLowerSeedCornerIso.{u}.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridLowerRectangle =
      nerveMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeLowerProjection _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridSeed (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint 2 1)) ≫
        nerveMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSeedInclusion := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  intro v
  apply Subtype.ext
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
