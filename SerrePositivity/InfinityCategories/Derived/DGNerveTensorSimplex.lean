module
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorSurvivingDifferential
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorErasedCandidateSum
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorCompositeCandidateSum
/-!
概要：同じ全切断候補の実 HA 右辺を同定し、全次元の HA を持つ実単体へ昇格する。
方針：元の実 cochain と HA 方程式を保ち、全面・退化への自然性を使う。
規約：tensor nerve と元の直積を同一視しない。使われ方：二変数 Hom の実 ∞ 関手化。
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
/-- 同じ全切断候補の実単体と全単体作用の構成。 -/
lemma dgNerveTensorCandidate_term {n : ℕ} (s : SimplexData R B n)
    (t : SimplexData R C n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (j : I.filter (fun x => a < x ∧ x < b)) :
    (dgNerveTensorDataCandidate R B C s t).term I a b k hI
      (ha.unique (I.isLeast_min' (Index.nonempty hI)))
      (hb.unique (I.isGreatest_max' (Index.nonempty hI))) hk
      j.val (Finset.mem_filter.mp j.property).1
      (Finset.mem_filter.mp j.property).2.1 (Finset.mem_filter.mp j.property).2.2 =
      dgNerveTensorCandidateDeletionTerm R B C s t I a b k hk ha hb j -
        dgNerveTensorCandidateCompositionTerm R B C s t I a b k hk ha hb j := by
  unfold SimplexData.term dgNerveTensorCandidateDeletionTerm dgNerveTensorCandidateCompositionTerm
  exact smul_sub _ _ _
/-- 同じ全切断候補の実単体と全単体作用の構成。 -/
lemma dgNerveTensorCandidate_rhs_eq_vertexSum {n : ℕ} (s : SimplexData R B n)
    (t : SimplexData R C n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b) :
    (dgNerveTensorDataCandidate R B C s t).rhs I a b k hI
      (ha.unique (I.isLeast_min' (Index.nonempty hI)))
      (hb.unique (I.isGreatest_max' (Index.nonempty hI))) hk =
      (∑ j : I.filter (fun x => a < x ∧ x < b),
        dgNerveTensorCandidateDeletionTerm R B C s t I a b k hk ha hb j) -
      (∑ j : I.filter (fun x => a < x ∧ x < b),
        dgNerveTensorCandidateCompositionTerm R B C s t I a b k hk ha hb j) := by
  unfold SimplexData.rhs
  rw [dgNerveInterior_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact dgNerveTensorCandidate_term R B C s t I a b k hk hI ha hb j
/-- 同じ全切断候補の実単体と全単体作用の構成。 -/
lemma dgNerveTensorBlockRhs_eq_candidate_rhs {n : ℕ}
    (s : Simplex R B n) (t : Simplex R C n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b) :
    dgNerveTensorBlockRhs R B C s.toSimplexData t.toSimplexData I a b k hk hI ha hb =
      (dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData).rhs I a b k hI
        (ha.unique (I.isLeast_min' (Index.nonempty hI)))
        (hb.unique (I.isGreatest_max' (Index.nonempty hI))) hk := by
  have hab : a < b := by
    have h := I.min'_lt_max'_of_card (by omega)
    simpa only [← ha.unique (I.isLeast_min' (Index.nonempty hI)),
      ← hb.unique (I.isGreatest_max' (Index.nonempty hI))] using h
  rw [dgNerveTensorBlockRhs_eq_survivingSums R B C s t I a b k hk hI ha hb hab,
    dgNerveTensorErasedCutSummand_sum, dgNerveTensorSelectedCompositeSummand_sum,
    dgNerveTensorCandidate_rhs_eq_vertexSum]

/-- 同じ全切断候補の実単体と全単体作用の構成。 -/
lemma dgNerveTensorDataCandidate_equation {n : ℕ}
    (s : Simplex R B n) (t : Simplex R C n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (Index.nonempty hI))
    (hb : b = I.max' (Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)) :
    differential R ((dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData).hom
      I a b k hI ha hb hk) =
      (dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData).rhs
        I a b k hI ha hb hk := by
  have haI : IsLeast (I : Set (Fin (n + 1))) a := by
    rw [ha]; exact I.isLeast_min' _
  have hbI : IsGreatest (I : Set (Fin (n + 1))) b := by
    rw [hb]; exact I.isGreatest_max' _
  change differential R (dgNerveTensorHomCandidate R B C s.toSimplexData t.toSimplexData
    I a b k hk hI haI hbI) = _
  rw [dgNerveTensorHomCandidate_differential_eq_blockRhs R B C s t I a b k hk hI haI hbI,
    dgNerveTensorBlockRhs_eq_candidate_rhs R B C s t I a b k hk hI haI hbI]
/-- 同じ全切断候補の実単体と全単体作用の構成。 -/
def dgNerveTensorSimplex {n : ℕ} (s : Simplex R B n) (t : Simplex R C n) :
    Simplex R (DGTensorCategory R B C) n where
  toSimplexData := dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData
  equation := dgNerveTensorDataCandidate_equation R B C s t

end SerrePositivity.InfinityCategories
