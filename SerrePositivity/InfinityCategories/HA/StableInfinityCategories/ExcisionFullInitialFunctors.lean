module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.InitialJoinIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCorePunctured
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridInitialPoint
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionSquareGrid
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetInteriorPrism
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PullbackConeVertex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ThinNerveConeComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ThinNerveMonomorphism

/-!
概要：比較格子の初期角を実引き戻しへ置換し、矢印圏の普遍性へ接続する。
方針：穿孔格子の同じ錐と全非初期単体を厳密に保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def excisionWithInitialToFull : WithInitial _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex.{u} ⥤
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} :=
  WithInitial.liftToInitial (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.posetSubtypeInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured)
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridInitialPoint_isInitial

def excisionFullToWithInitial : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⥤
    WithInitial _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex.{u} := by
  classical
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullWithInitial_isThin.{u}
  refine {
    obj := fun p ↦ if hp : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured p
      then WithInitial.of ⟨p, hp⟩ else WithInitial.star
    map := ?_
    map_id := fun _ ↦ Subsingleton.elim _ _
    map_comp := fun _ _ ↦ Subsingleton.elim _ _ }
  intro p q f
  split_ifs with hp hq
  · exact homOfLE (leOfHom f)
  · have hf := leOfHom f
    change p.down.val.1.val ≤ q.down.val.1.val ∧
      p.down.val.2.val ≤ q.down.val.2.val at hf
    change 1 ≤ p.down.val.1.val + p.down.val.2.val at hp
    change ¬ 1 ≤ q.down.val.1.val + q.down.val.2.val at hq
    omega
  · exact PUnit.unit
  · exact PUnit.unit

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
