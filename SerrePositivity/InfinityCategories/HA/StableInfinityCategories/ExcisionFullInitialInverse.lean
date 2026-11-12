module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.InitialJoinIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCorePunctured
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullInitialFunctors
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

lemma excisionWithInitialToFull_after_inverse (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionWithInitialToFull.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullToWithInitial.obj p) = p := by
  classical
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionWithInitialToFull.obj (if hp : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured p
    then WithInitial.of ⟨p, hp⟩ else WithInitial.star) = p
  by_cases hp : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured p
  · rw [dite_eq_left hp]
    rfl
  · rw [dite_eq_right hp]
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridInitialPoint = p
    apply ULift.ext
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · change 0 = p.down.val.1.val
      change ¬ 1 ≤ p.down.val.1.val + p.down.val.2.val at hp
      omega
    · change 0 = p.down.val.2.val
      change ¬ 1 ≤ p.down.val.1.val + p.down.val.2.val at hp
      omega

lemma excisionFullToWithInitial_after_inverse (p : WithInitial
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionFullToWithInitial.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionWithInitialToFull.obj p) = p := by
  classical
  cases p with
  | of p =>
    change (if hp : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured p.val then WithInitial.of ⟨p.val, hp⟩
      else WithInitial.star) = WithInitial.of p
    rw [dite_eq_left p.property]
  | star =>
    change (if hp : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsExcisionFullPunctured _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridInitialPoint
      then WithInitial.of (⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridInitialPoint.{u}, hp⟩ :
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionFullPuncturedIndex.{u}) else WithInitial.star) =
        WithInitial.star
    rw [dite_eq_right (by change ¬ (1 : ℕ) ≤ 0 + 0; decide)]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
