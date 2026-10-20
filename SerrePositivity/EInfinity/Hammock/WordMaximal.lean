module

public import SerrePositivity.EInfinity.Hammock.WordAlternating
public import Mathlib.Data.Fintype.EquivFin

/-!
# 正の最大長の二つの交互方向語

概要：長さ n+1 の交互方向語を初期方向と同値な型としてまとめる。
方針：既存の分類と二つの語の区別を使う。
規約：元の語を保持する部分型であり、同型類に置き換えない。
使われ方：長さ段階の有限個の貼り合わせ。
-/

@[expose] public section
noncomputable section
namespace SerrePositivity.EInfinity.Hammock.Word

abbrev MaximalAlternating (n : ℕ) := {a : Word // a.length = n + 1 ∧ IsAlternating a}

def maximalAlternating (n : ℕ) (d : Direction) : MaximalAlternating n :=
  ⟨alternating (n + 1) d, rfl, alternating_isAlternating (n + 1) d⟩

lemma maximalAlternating_bijective (n : ℕ) : Function.Bijective (maximalAlternating n) := by
  constructor
  · intro d e h
    have he := congrArg Subtype.val h
    cases d <;> cases e
    · rfl
    · exact False.elim (alternating_ne n he)
    · exact False.elim (alternating_ne n he.symm)
    · rfl
  · intro a
    obtain ⟨d, hd⟩ := exists_alternating a.val a.property.2
    refine ⟨d, Subtype.ext ?_⟩
    change alternating (n + 1) d = a.val
    simpa only [a.property.1] using hd.symm

def maximalAlternatingEquiv (n : ℕ) : Direction ≃ MaximalAlternating n :=
  Equiv.ofBijective (maximalAlternating n) (maximalAlternating_bijective n)

lemma maximalAlternating_finite (n : ℕ) : Finite (MaximalAlternating n) := by
  have hd : Function.Injective (fun d : Direction => decide (d = .forward)) := by
    intro d e h
    cases d <;> cases e <;> simp_all
  let : Finite Direction := Finite.of_injective _ hd
  exact Finite.of_surjective (maximalAlternating n) (maximalAlternating_bijective n).2

end SerrePositivity.EInfinity.Hammock.Word
