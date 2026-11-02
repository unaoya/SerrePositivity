module
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialJoinIso
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.Stable.ExcisionCorePunctured
public import SerrePositivity.InfinityCategories.Stable.ExcisionFullPuncturedCones
public import SerrePositivity.InfinityCategories.Stable.ExcisionFullPuncturedIndex
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

lemma excisionFullWithInitial_isThin : Quiver.IsThin
    (WithInitial ExcisionFullPuncturedIndex.{u}) := by
  intro a b
  cases a <;> cases b
  all_goals
    change Subsingleton (WithInitial.Hom _ _)
    dsimp only [WithInitial.Hom]
    infer_instance

def excisionGridInitialPoint : ExcisionGridIndex.{u} :=
  (excisionGridCorePoint 0 0).val.val

def excisionGridInitialPoint_isInitial : IsInitial excisionGridInitialPoint.{u} :=
  IsInitial.ofUniqueHom (fun _ ↦ homOfLE ⟨Nat.zero_le _, Nat.zero_le _⟩)
    (fun _ _ ↦ Subsingleton.elim _ _)

end SerrePositivity.InfinityCategories
