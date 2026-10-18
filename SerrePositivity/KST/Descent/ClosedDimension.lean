module

public import Mathlib.Topology.KrullDimension

/-!
# 整な基底の真閉部分における次元低下

## 概要
有限な次元上界 d を持つ既約空間の真閉部分の次元は d より小さい。

## 方針
真閉部分の既約閉集合の鎖を全空間まで一段延長する。
形式的には `WithTop` の厳密単調写像と Krull 次元の一段増加を使う。

## 規約
有限の自然数上界を明示する。無限次元で真に次元が下がるとは主張しない。
空の閉部分は次元 ⊥ のまま扱い、零次元へ丸めない。

## 使われ方
論文 補題 3.3 と定理 3.1 の整スキーム上の次元帰納、公理 (7)。
-/

@[expose] public section

open Order TopologicalSpace Topology Set

namespace SerrePositivity.KST.Descent

/-- 概要：有限な次元上界 d を持つ既約空間の真閉部分の次元は d 未満（論文 §3）。
方針：真閉部分の既約閉集合を全空間へ送り、全空間を加えて鎖を一段伸ばす。
規約：次元は `WithBot ℕ∞`、上界 d は自然数。Noether 性はこの補題には不要。
使われ方：補題 3.3 の平坦化中心と定理 3.1 の section の一致場所での帰納。 -/
theorem topologicalKrullDim_properClosed_lt_bound
    {X : Type*} [TopologicalSpace X] [IrreducibleSpace X]
    (Z : Set X) (closed : IsClosed Z) (proper : Z ≠ univ)
    (d : ℕ) (bound : topologicalKrullDim X ≤ d) : topologicalKrullDim Z < d := by
  classical
  by_cases h : Nonempty (IrreducibleCloseds Z)
  · have := h
    let whole : IrreducibleCloseds X := ⟨univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
    let pushForward : IrreducibleCloseds Z → IrreducibleCloseds X :=
      IrreducibleCloseds.map Subtype.val continuous_subtype_val
    have below (s : IrreducibleCloseds Z) : pushForward s < whole := by
      have hsub : (pushForward s : Set X) ⊆ Z := by
        change closure (Subtype.val '' (s : Set Z)) ⊆ Z
        refine closure_minimal ?_ closed
        rintro _ ⟨z, _, rfl⟩
        exact z.property
      refine lt_iff_le_not_ge.mpr ⟨Set.subset_univ _, ?_⟩
      intro hle
      apply proper
      apply Set.eq_univ_of_forall
      intro x
      exact hsub (hle (by trivial))
    have strict : StrictMono (WithTop.recTopCoe whole pushForward) :=
      WithTop.strictMono_iff.mpr
        ⟨IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal, below⟩
    have hdim := (krullDim_le_of_strictMono _ strict).trans bound
    rw [krullDim_WithTop] at hdim
    exact ENat.WithBot.add_one_le_natCast_iff.mp hdim
  · have : IsEmpty (IrreducibleCloseds Z) := not_nonempty_iff.mp h
    simp only [topologicalKrullDim, krullDim_eq_bot]
    exact WithBot.bot_lt_coe _

/-- 概要：有限次元が d である既約空間の真閉部分では次元が真に下がる（論文 §3）。
方針：有限な次元上界についての補題を、実際の次元の等式に適用する。
規約：有限性を明示するため、実際の次元と自然数 d の等式を引数とする。
使われ方：整スキームの真閉部分に対する公理 (7) の次元低下。 -/
theorem topologicalKrullDim_properClosed_lt
    {X : Type*} [TopologicalSpace X] [IrreducibleSpace X]
    (Z : Set X) (closed : IsClosed Z) (proper : Z ≠ univ)
    (d : ℕ) (dimension : topologicalKrullDim X = d) :
    topologicalKrullDim Z < topologicalKrullDim X := by
  rw [dimension]
  exact topologicalKrullDim_properClosed_lt_bound Z closed proper d dimension.le

end SerrePositivity.KST.Descent
