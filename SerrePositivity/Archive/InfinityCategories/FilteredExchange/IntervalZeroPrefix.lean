module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RightPrismPrefixEquality

/-!
概要：外側零時間の先頭区間では、元の時刻を零へ置き換えても係数が一致する。
方針：空区間と非空区間に分け、元の各頂点の値を使う。
規約：同じ係数の制限を保持。使われ方：実三角形の長辺の厳密回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ先頭区間上で零の時間は、元の零定値時間と同じ係数付き制限を持つ。 -/
lemma interval_zero_prefix {P : SSet.{u}} {n : ℕ} (s : (Δ[1] : SSet.{u}) _⦋n⦌)
    (p : P _⦋n⦌) (r : ℕ) (hr : r ≤ n + 1)
    (hs : ∀ i : Fin (n + 1), i.val < r → s i = 0) :
    Join.augMap (Δ[1] ⊗ P) (Join.prefixIncl (n + 1) r hr) (s, p) =
      Join.augMap (Δ[1] ⊗ P) (Join.prefixIncl (n + 1) r hr)
        (PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) n, p) := by
  cases r with
  | zero => rfl
  | succ r =>
    apply Prod.ext
    · apply stdSimplex.ext
      intro i
      exact hs ⟨i.val, lt_of_lt_of_le i.isLt hr⟩ i.isLt
    · rfl

end SerrePositivity.InfinityCategories.F2
