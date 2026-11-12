module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCorePoint

/-!
概要：実比較格子の 3×3 部分の座標交換。
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

def excisionGridCoreTranspose : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} ≃o _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} where
  toFun p := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint
    ⟨p.val.val.down.val.2.val, Nat.lt_succ_of_le p.property.2⟩
    ⟨p.val.val.down.val.1.val, Nat.lt_succ_of_le p.property.1⟩
  invFun p := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint
    ⟨p.val.val.down.val.2.val, Nat.lt_succ_of_le p.property.2⟩
    ⟨p.val.val.down.val.1.val, Nat.lt_succ_of_le p.property.1⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply ULift.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply ULift.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> rfl
  map_rel_iff' := by
    intro a b
    exact and_comm

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
