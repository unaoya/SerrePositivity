module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Discrete.Basic
/-!
# 離散圏の元の nerve と定数単体集合の同型

概要：元の離散圏の nerve の全単体を同じ値へ厳密に回収する。
方針：元の全射列の値と同じ端点の移送を使い、元の全縦射を保持する。
規約：モデル構造は要求せず、元の比較射を使う。
使われ方：DK5.7の元の単一列の Hom の弱比較への接続。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteNerveIso
open CategoryTheory Opposite

def simplexEquiv (T : Type u) (n : ℕ) : ComposableArrows (Discrete T) n ≃ T where
  toFun c := (c.obj 0).as
  invFun t := (Functor.const (Fin (n + 1))).obj (Discrete.mk t)
  left_inv c := by
    refine CategoryTheory.Functor.ext (fun i => ?_) ?_
    · change Discrete.mk (c.obj 0).as = c.obj i
      exact Discrete.ext (Discrete.eq_of_hom (c.map (homOfLE (Fin.zero_le i))))
    · intro i j h
      exact Subsingleton.elim _ _
  right_inv _ := rfl

def iso (T : Type u) : nerve (Discrete T) ≅ (Functor.const SimplexCategoryᵒᵖ).obj T :=
  NatIso.ofComponents (fun n => Equiv.toIso (simplexEquiv T n.unop.len)) (by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro c
    exact (Discrete.eq_of_hom (c.map (homOfLE (Fin.zero_le
      (θ.unop.toOrderHom 0))))).symm)
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiscreteNerveIso
