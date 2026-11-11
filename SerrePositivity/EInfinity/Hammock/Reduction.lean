module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordMerge
public import SerrePositivity.EInfinity.Hammock.EraseSimplex
public import Mathlib.Logic.Relation

/-!
# 元の未縮約 hammock の二つの基本縮約

概要：同方向二列の合成と全行恒等な一列の削除を、元の全単体上の関係として構成。
方針：元の語の写像と構成済みの全射列の削除を使う。
規約：各基本縮約は長さを減らし、元の余極限内の値を保持する。
使われ方：縮約停止性・合流性と縮約 hammock の構成。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C) (n : SimplexCategoryᵒᵖ)

/-- 原典の元の全射列に対する、長さを一つ減らす二つの基本縮約。 -/
inductive Reduction : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n → Prop
  | merge {k : ℕ} (d : Fin (k + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p : Fin (k + 1))
      (hp : d p.castSucc = d p.succ) (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (⟨k + 2, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) X Y).obj n) :
      Reduction ⟨⟨k + 2, d⟩, τ⟩
        ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeTarget d p, ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d p hp)).app n τ⟩
  | erase {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (j : Fin w.length) (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y).obj n)
      (hτ : ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj k) j) :
      Reduction ⟨w, τ⟩ ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase w j, eraseSimplex W X Y j τ hτ⟩

namespace Reduction
variable {W X Y n}

lemma length_lt {r s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n} (h : Reduction W X Y n r s) :
    s.1.length < r.1.length := by
  cases h with
  | merge d p hp τ => exact Nat.lt_succ_self _
  | erase j τ hτ => exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase_length_lt _ j

lemma value_eq {r s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n} (h : Reduction W X Y n r s) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.value W X Y r = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.value W X Y s := by
  cases h with
  | merge d p hp τ => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.value_transition W X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d p hp) τ).symm
  | erase j τ hτ =>
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.value_transition W X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion _ j)
      (eraseSimplex W X Y j τ hτ)
    rw [eraseSimplex_fac] at he
    exact he

lemma chain_value_eq {r s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n}
    (h : Relation.ReflTransGen (Reduction W X Y n) r s) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.value W X Y r = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.value W X Y s := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (value_eq hs)

end Reduction
end SerrePositivity.EInfinity.Hammock
