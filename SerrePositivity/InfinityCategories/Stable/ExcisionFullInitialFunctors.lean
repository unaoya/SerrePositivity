module
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialJoinIso
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.Stable.ExcisionCorePunctured
public import SerrePositivity.InfinityCategories.Stable.ExcisionFullPuncturedIndex
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridInitialPoint
public import SerrePositivity.InfinityCategories.Stable.ExcisionSquareGrid
public import SerrePositivity.InfinityCategories.Stable.PosetInteriorPrism
public import SerrePositivity.InfinityCategories.Stable.PullbackConeVertex
public import SerrePositivity.InfinityCategories.Stable.ThinNerveConeComparison
public import SerrePositivity.InfinityCategories.Stable.ThinNerveMonomorphism

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
namespace SerrePositivity.InfinityCategories

def excisionWithInitialToFull : WithInitial ExcisionFullPuncturedIndex.{u} ⥤
    ExcisionGridIndex.{u} :=
  WithInitial.liftToInitial (posetSubtypeInclusion IsExcisionFullPunctured)
    excisionGridInitialPoint_isInitial

def excisionFullToWithInitial : ExcisionGridIndex.{u} ⥤
    WithInitial ExcisionFullPuncturedIndex.{u} := by
  classical
  have := excisionFullWithInitial_isThin.{u}
  refine {
    obj := fun p ↦ if hp : IsExcisionFullPunctured p
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

end SerrePositivity.InfinityCategories
