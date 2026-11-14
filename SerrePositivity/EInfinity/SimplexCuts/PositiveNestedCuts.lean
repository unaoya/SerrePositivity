module

public import SerrePositivity.EInfinity.SimplexCuts.PositiveCompositeCuts
public import SerrePositivity.EInfinity.SimplexCuts.RawAction
public import SerrePositivity.EInfinity.SimplexCuts.ColorOccurrenceBoundaries
public import SerrePositivity.EInfinity.SimplexCuts.IntervalBoundaryGlue

/-!
# 正の内側 arity の二段切断の全添字

Berger–Fresse §2.2.6、M14 L12a。
外側の元の切断と、その指定色の出力次数における内側の元の切断を組にする。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の外側の切断と、その指定色の全頂点列の元の内側切断（BF §2.2.6）。 -/
abbrev PositiveNestedCutIndex {m n d e : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (_v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1)) (q : ℕ) :=
  Σ s : Cut (m + d) q, Cut (n + e) (outputDegree s (positiveWord u) k)

/-- C357：同じ語長の等式移送は、指定色の出現回数を保つ（BF §1.2.4）。 -/
lemma positiveWord_occurrenceCount {m d : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (k : Fin (m + 1)) :
    Surjection.occurrenceCount (positiveWord u).val k = Surjection.occurrenceCount u.val k := by
  unfold positiveWord Surjection.occurrenceCount
  exact congrArg (fun l : List (Fin (m + 1)) => l.count k)
    (word_eq_mp_ofFn (by omega : (m + 1) + d = m + d + 1) u)

end SerrePositivity.EInfinity.SimplexCuts
