module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex

/-!
概要：比較格子の実 3×3 部分の頂点と順序。
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

def excisionGridCorePoint (i j : Fin 3) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreIndex.{u} := by
  let x : Fin 4 := ⟨i.val, by omega⟩
  let y : Fin 4 := ⟨j.val, by omega⟩
  let p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} := ULift.up ⟨(x, y), by dsimp [x, y]; omega⟩
  have hp : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridCore p := by dsimp [p, x, y, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionGridCore]; omega
  exact ⟨⟨p, Or.inl hp⟩, hp⟩

lemma excisionGridCorePoint_le {i i' j j' : Fin 3} (hi : i ≤ i') (hj : j ≤ j') :
    excisionGridCorePoint.{u} i j ≤ excisionGridCorePoint i' j' := ⟨hi, hj⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
