module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RightPrismPrefixEquality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SquareUpperRetraction

/-!
概要：右 join prism は、終点側の内側時間を最大値へ置き換えても変わらない。
方針：外側零時間の先頭上では、最大値は元の内側時間と一致する。
規約：実全図式の厳密等式を使う。使われ方：元の合成四角形全体の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 外側時間が零の先頭区間では、二時刻の最大値は元の内側時間。 -/
lemma squareUpperMaximum_prefix {P : SSet.{u}} {n : ℕ}
    (s t : (Δ[1] : SSet.{u}) _⦋n⦌) (p : P _⦋n⦌) (r : ℕ) (hr : r ≤ n + 1)
    (hs : ∀ i : Fin (n + 1), i.val < r → s i = 0) :
    Join.augMap (Δ[1] ⊗ P) (Join.prefixIncl (n + 1) r hr)
        ((squareUpperMaximum.app (Opposite.op ⦋n⦌) (s, t)), p) =
      Join.augMap (Δ[1] ⊗ P) (Join.prefixIncl (n + 1) r hr) (t, p) := by
  cases r with
  | zero => rfl
  | succ r =>
    apply Prod.ext
    · apply stdSimplex.ext
      intro i
      change max (s ⟨i.val, lt_of_lt_of_le i.isLt hr⟩)
        (t ⟨i.val, lt_of_lt_of_le i.isLt hr⟩) = t ⟨i.val, lt_of_lt_of_le i.isLt hr⟩
      rw [hs _ i.isLt]
      exact max_eq_right (Fin.zero_le _)
    · rfl

/-- 元の右 join prism は、同じ先頭区間を保つ最大値への置換で厳密に不変。 -/
lemma rightMappingSpacePrism_upper_retraction (P : SSet.{u}) :
    squareUpperRetraction P ≫ rightMappingSpacePrism (Δ[1] ⊗ P) =
      rightMappingSpacePrism (Δ[1] ⊗ P) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t, p⟩
  change (rightMappingSpacePrism (Δ[1] ⊗ P)).app (Opposite.op ⦋n⦌)
      (s, (squareUpperMaximum.app (Opposite.op ⦋n⦌) (s, t), p)) = _
  apply rightMappingSpacePrism_eq_of_prefix
  apply squareUpperMaximum_prefix
  intro i hi
  rw [intervalJoin_cut] at hi
  have h := (Join.lt_pullCut_iff (stdSimplex.objEquiv s).toOrderHom 1 i).mp hi
  change (s i).val < 1 at h
  exact Fin.ext (Nat.le_zero.mp (Nat.le_of_lt_succ h))

end SerrePositivity.InfinityCategories.F2
