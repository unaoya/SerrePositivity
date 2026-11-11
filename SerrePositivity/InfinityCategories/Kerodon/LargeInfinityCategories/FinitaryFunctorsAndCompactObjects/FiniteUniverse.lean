module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
概要：有限単体集合の非退化単体と有限性は、任意の宇宙持ち上げで変わらない。
方針：退化表示を同じ単体作用素と ULift の往復で移し、全非退化単体の全単射を作る。
規約：元の単体と次数を保持。使われ方：filtered 添字の宇宙持ち上げでの有限試験。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 同じ単体は、宇宙持ち上げの前後で同じ退化表示を持つ。 -/
lemma ulift_mem_degenerate_iff (X : SSet.{u}) {n : ℕ} (x : X _⦋n⦌) :
    ULift.up x ∈ ((SSet.uliftFunctor.{v, u}).obj X).degenerate n ↔ x ∈ X.degenerate n := by
  rw [SSet.mem_degenerate_iff, SSet.mem_degenerate_iff]
  constructor
  · rintro ⟨m, hm, f, hf, y, hy⟩
    exact ⟨m, hm, f, hf, y.down, congrArg ULift.down hy⟩
  · rintro ⟨m, hm, f, hf, y, hy⟩
    exact ⟨m, hm, f, hf, ULift.up y, congrArg ULift.up hy⟩

/-- 元の全非退化単体を、次数と元の単体を保って宇宙持ち上げから回収する。 -/
def uliftNondegenerateEquiv (X : SSet.{u}) :
    ((SSet.uliftFunctor.{v, u}).obj X).N ≃ X.N where
  toFun s := SSet.N.mk s.simplex.down (by
    have hs := s.nonDegenerate
    rw [SSet.mem_nonDegenerate_iff_notMem_degenerate] at hs ⊢
    exact fun h => hs ((ulift_mem_degenerate_iff X _).mpr h))
  invFun s := SSet.N.mk (ULift.up s.simplex) (by
    rw [SSet.mem_nonDegenerate_iff_notMem_degenerate]
    exact fun h => s.nonDegenerate ((ulift_mem_degenerate_iff X _).mp h))
  left_inv s := by cases s; rfl
  right_inv s := by cases s; rfl

/-- 有限性は、同じ全非退化単体の宇宙持ち上げで保存・反映される。 -/
lemma finite_ulift_iff (X : SSet.{u}) :
    SSet.Finite ((SSet.uliftFunctor.{v, u}).obj X) ↔ SSet.Finite X := by
  constructor
  · intro h
    exact ⟨Finite.of_equiv _ (uliftNondegenerateEquiv.{u, v} X)⟩
  · intro h
    exact ⟨Finite.of_equiv _ (uliftNondegenerateEquiv.{u, v} X).symm⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
