module
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorSelectedNormalization
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorUnselectedNormalization
/-!
概要：実 tensor の両寄与の全和から内部項を消し、削除と左右合成だけを残す。
方針：各実項の分解と同じ削除・挿入添字による内部和の相殺を使う。
規約：同じ全次数の cochain を使う。使われ方：全次元 HA の右辺の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped BigOperators
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
/-- 二つの元の寄与の全和と残る境界項の比較。 -/
lemma dgNerveTensorContributions_sum_eq_erased_sub_composite {n : ℕ} (s : SimplexData R B n)
    (t : SimplexData R C n) (I T : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (hT : ∀ x ∈ T, x ∈ I ∧ a < x ∧ x < b) (hab : a < b) :
    (∑ p : DGNerveCutDeletionIndex T,
      dgNerveTensorSelectedContribution R B C s t I T a b k hk hI ha hb hT hab p) +
    (∑ p : DGNerveCutInsertionIndex T,
      dgNerveTensorUnselectedContribution R B C s t I T a b k hk ha hb hT hab p) =
    (∑ p : DGNerveCutInsertionIndex T,
      dgNerveTensorErasedCutSummand R B C s t I T a b k hk ha hb hT p) -
    (∑ p : DGNerveCutDeletionIndex T,
      dgNerveTensorSelectedCompositeSummand R B C s t I T a b k hk ha hb hT p) := by
  have hsel := fun p => dgNerveTensorSelectedTerm_eq_internal_sub_composite
    R B C s t I T a b k hk hI ha hb hT hab p
  have hunsel := fun p => dgNerveTensorUnselectedContribution_eq_erased_sub_internal
    R B C s t I T a b k hk hI ha hb hT hab p
  simp_rw [hsel, hunsel]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    dgNerveTensorInternalSums_eq R B C s t I T a b k hk hI ha hb hT hab]
  abel
end SerrePositivity.InfinityCategories
