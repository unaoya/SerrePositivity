module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAlternating
public import Mathlib.Data.Fintype.EquivFin

/-!
# 正の最大長の二つの交互方向語

概要：長さ n+1 の交互方向語を初期方向と同値な型としてまとめる。
方針：既存の分類と二つの語の区別を使う。
規約：元の語を保持する部分型であり、同型類に置き換えない。
使われ方：長さ段階の有限個の貼り合わせ。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

abbrev MaximalAlternating (n : ℕ) := {a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word // a.length = n + 1 ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.IsAlternating a}

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (MaximalAlternating)


def maximalAlternating (n : ℕ) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) : MaximalAlternating n :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.alternating (n + 1) d, rfl, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.alternating_isAlternating (n + 1) d⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (maximalAlternating)


lemma maximalAlternating_bijective (n : ℕ) : Function.Bijective (maximalAlternating n) := by
  constructor
  · intro d e h
    have he := congrArg Subtype.val h
    cases d <;> cases e
    · rfl
    · exact False.elim (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.alternating_ne n he)
    · exact False.elim (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.alternating_ne n he.symm)
    · rfl
  · intro a
    obtain ⟨d, hd⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.exists_alternating a.val a.property.2
    refine ⟨d, Subtype.ext ?_⟩
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.alternating (n + 1) d = a.val
    simpa only [a.property.1] using hd.symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (maximalAlternating_bijective)


def maximalAlternatingEquiv (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction ≃ MaximalAlternating n :=
  Equiv.ofBijective (maximalAlternating n) (maximalAlternating_bijective n)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (maximalAlternatingEquiv)


lemma maximalAlternating_finite (n : ℕ) : Finite (MaximalAlternating n) := by
  have hd : Function.Injective (fun d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction => decide (d = .forward)) := by
    intro d e h
    cases d <;> cases e <;> simp_all
  let : Finite _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction := Finite.of_injective _ hd
  exact Finite.of_surjective (maximalAlternating n) (maximalAlternating_bijective n).2

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (maximalAlternating_finite)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
