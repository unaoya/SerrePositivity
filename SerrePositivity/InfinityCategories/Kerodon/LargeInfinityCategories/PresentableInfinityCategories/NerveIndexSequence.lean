module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
概要：元の poset の nerve 内の可算全図式から、元の poset 内の増大列を回収する。
方針：全図式の頂点を読み、元の順序射の像を nerve の実射へ戻す。
規約：対象列を選び直さない。使われ方：小さい種集合を含む共終な可算部分表示。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 元の添字図式が実際に取る、元の poset の対象列。 -/
def nerveIndexSequence {A : Type u} [Preorder A]
    (J : nerve (ULift.{u} ℕ) ⟶ nerve A) : ℕ → A :=
  fun n ↦ nerveEquiv (J.app (Opposite.op ⦋0⦌)
    ((nerveEquiv (C := ULift.{u} ℕ)).symm (ULift.up n)))

/-- 全添字図式の元の順序射は、回収した同じ対象列の単調性を保証する。 -/
lemma nerveIndexSequence_monotone {A : Type u} [Preorder A]
    (J : nerve (ULift.{u} ℕ) ⟶ nerve A) : Monotone (nerveIndexSequence J) := by
  intro n m h
  let f : (ULift.up n : ULift.{u} ℕ) ⟶ ULift.up m := homOfLE h
  let e := (CategoryTheory.nerve.edgeMk f).map J
  exact leOfHom (CategoryTheory.nerve.homEquiv e)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
