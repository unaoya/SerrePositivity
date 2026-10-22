module
public import SerrePositivity.InfinityCategories.Stable.ExcisionFullPuncturedIndex
public import SerrePositivity.InfinityCategories.Stable.PosetInteriorPrism
public import SerrePositivity.InfinityCategories.Stable.ExcisionCorePunctured
public import SerrePositivity.InfinityCategories.Stable.ThinNerveMonomorphism
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialJoinIso
public import SerrePositivity.InfinityCategories.Stable.ThinNerveConeComparison
public import SerrePositivity.InfinityCategories.Stable.PullbackConeVertex
public import SerrePositivity.InfinityCategories.F2.ConeValEquality
public import SerrePositivity.InfinityCategories.Stable.ExcisionSquareGrid
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanBoundary

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

def excisionCorePuncturedToFull :
    ExcisionCorePuncturedIndex.{u} →o ExcisionFullPuncturedIndex.{u} where
  toFun p := ⟨p.val.val.val, p.property⟩
  monotone' _ _ h := h

def excisionFullPuncturedToCore :
    ExcisionFullPuncturedIndex.{u} →o ExcisionCorePuncturedIndex.{u} where
  toFun p := by
    let x : Fin 3 := ⟨min p.val.down.val.1.val 2, by omega⟩
    let y : Fin 3 := ⟨min p.val.down.val.2.val 2, by omega⟩
    exact ⟨excisionGridCorePoint x y, by
      have hp := p.property
      change 1 ≤ p.val.down.val.1.val + p.val.down.val.2.val at hp
      change 1 ≤ min p.val.down.val.1.val 2 + min p.val.down.val.2.val 2
      omega⟩
  monotone' := by
    intro a b h
    constructor
    · change min a.val.down.val.1.val 2 ≤ min b.val.down.val.1.val 2
      exact min_le_min h.1 le_rfl
    · change min a.val.down.val.2.val 2 ≤ min b.val.down.val.2.val 2
      exact min_le_min h.2 le_rfl

lemma excisionFullPuncturedToCore_section : Function.LeftInverse
    excisionFullPuncturedToCore.{u} excisionCorePuncturedToFull := by
  intro p
  have hp := p.val.property
  change p.val.val.val.down.val.1.val ≤ 2 ∧ p.val.val.val.down.val.2.val ≤ 2 at hp
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · change min p.val.val.val.down.val.1.val 2 = p.val.val.val.down.val.1.val
    exact min_eq_left hp.1
  · change min p.val.val.val.down.val.2.val 2 = p.val.val.val.down.val.2.val
    exact min_eq_left hp.2

lemma excisionFullPuncturedToCore_le (p : ExcisionFullPuncturedIndex.{u}) :
    excisionCorePuncturedToFull (excisionFullPuncturedToCore p) ≤ p := by
  constructor
  · change min p.val.down.val.1.val 2 ≤ p.val.down.val.1.val
    exact Nat.min_le_left _ _
  · change min p.val.down.val.2.val 2 ≤ p.val.down.val.2.val
    exact Nat.min_le_left _ _

end SerrePositivity.InfinityCategories
