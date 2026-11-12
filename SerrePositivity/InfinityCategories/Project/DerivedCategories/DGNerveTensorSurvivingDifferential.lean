module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveInteriorUnselectedSum
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveTensorBlockDifferential
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveTensorContributionsSum
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveTensorCutNormalDifferential
/-!
概要：元の tensor 候補の微分と block 右辺を、内部相殺後の残存和へ同定する。
方針：同じ集合・点・cochain を保つ実添字比較を使う。
規約：元の全次数で同定する。使われ方：全次元 HA の右辺の照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory DifferentialGraded
universe w
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 元の全添字と同じ実境界成分の比較。 -/
lemma dgNerveTensorHomCandidate_differential_eq_contributions {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) (hab : a < b) :
    differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate R B C s.toSimplexData t.toSimplexData
      I a b k hk hI ha hb) =
    (∑ p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutDeletionIndex (I.filter (fun j => a < j ∧ j < b)),
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorSelectedContribution R B C s.toSimplexData t.toSimplexData
        I (I.filter (fun j => a < j ∧ j < b)) a b k hk hI ha hb
        (fun _ hx => Finset.mem_filter.mp hx) hab p) +
    (∑ p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutInsertionIndex (I.filter (fun j => a < j ∧ j < b)),
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorUnselectedContribution R B C s.toSimplexData t.toSimplexData
        I (I.filter (fun j => a < j ∧ j < b)) a b k hk ha hb
        (fun _ hx => Finset.mem_filter.mp hx) hab p) := by
  let T := I.filter (fun j => a < j ∧ j < b)
  have hT : ∀ x ∈ T, x ∈ I ∧ a < x ∧ x < b := fun _ hx => Finset.mem_filter.mp hx
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_sum (A := R) (D := DGTensorCategory R B C),
    ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutDeletionSigma_sum T, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutInsertionSigma_sum T,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  have hc : ∀ j ∈ S.val, j ∈ I ∧ a < j ∧ j < b :=
    fun _ hx => hT _ (Finset.mem_powerset.mp S.property hx)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm_differential_normal R B C s t I a b S.val k hk hI ha hb hc hab,
    smul_add]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [Finset.smul_sum]
    rfl
  · rw [Finset.smul_sum, Finset.smul_sum]
    trans ∑ j : I, if h : a < j.val ∧ j.val < b ∧ j.val ∉ S.val then
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b S.val).negOnePow •
        ((-(S.val.card : ℤ)).negOnePow • _root_.SerrePositivity.DifferentialGraded.dgTensorElement R (n := k + 1)
          (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
          (y := ((s.obj b, t.obj b) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveSelectedCutHom R B s.toSimplexData a b S.val hab (fun x hx => (hc x hx).2))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundaryTerm R C t.toSimplexData I a b S.val j.val
            (2 - (I.card : ℤ) + (S.val.card : ℤ)) rfl ha hb hc j.property
            h.1 h.2.1 h.2.2) (by omega)) else 0
    · apply Finset.sum_congr rfl
      intro j _
      split_ifs with h
      · rfl
      · simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_zero_right, smul_zero]
    · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveInteriorUnselected_sum I S.val a b (fun j hj haj hjb hjS =>
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign I a b S.val).negOnePow •
          ((-(S.val.card : ℤ)).negOnePow • _root_.SerrePositivity.DifferentialGraded.dgTensorElement R (n := k + 1)
            (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
            (y := ((s.obj b, t.obj b) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveSelectedCutHom R B s.toSimplexData a b S.val hab
              (fun x hx => (hc x hx).2))
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutBoundaryTerm R C t.toSimplexData I a b S.val j
              (2 - (I.card : ℤ) + (S.val.card : ℤ)) rfl ha hb hc hj haj hjb hjS) (by omega)))
/-- 元の全添字と同じ実境界成分の比較。 -/
lemma dgNerveTensorHomCandidate_differential_eq_survivingSums {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) (hab : a < b) :
    differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate R B C s.toSimplexData t.toSimplexData
      I a b k hk hI ha hb) =
    (∑ p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutInsertionIndex (I.filter (fun j => a < j ∧ j < b)),
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorErasedCutSummand R B C s.toSimplexData t.toSimplexData
        I (I.filter (fun j => a < j ∧ j < b)) a b k hk ha hb
        (fun _ hx => Finset.mem_filter.mp hx) p) -
    (∑ p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutDeletionIndex (I.filter (fun j => a < j ∧ j < b)),
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorSelectedCompositeSummand R B C s.toSimplexData t.toSimplexData
        I (I.filter (fun j => a < j ∧ j < b)) a b k hk ha hb
        (fun _ hx => Finset.mem_filter.mp hx) p) := by
  rw [dgNerveTensorHomCandidate_differential_eq_contributions R B C s t I a b k hk hI ha hb hab]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorContributions_sum_eq_erased_sub_composite R B C s.toSimplexData t.toSimplexData
    I (I.filter (fun j => a < j ∧ j < b)) a b k hk hI ha hb
    (fun _ hx => Finset.mem_filter.mp hx) hab
/-- 元の全添字と同じ実境界成分の比較。 -/
lemma dgNerveTensorBlockRhs_eq_survivingSums {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card)
    (ha : IsLeast (I : Set (Fin (n + 1))) a)
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) (hab : a < b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorBlockRhs R B C s.toSimplexData t.toSimplexData I a b k hk hI ha hb =
    (∑ p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutInsertionIndex (I.filter (fun j => a < j ∧ j < b)),
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorErasedCutSummand R B C s.toSimplexData t.toSimplexData
        I (I.filter (fun j => a < j ∧ j < b)) a b k hk ha hb
        (fun _ hx => Finset.mem_filter.mp hx) p) -
    (∑ p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutDeletionIndex (I.filter (fun j => a < j ∧ j < b)),
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorSelectedCompositeSummand R B C s.toSimplexData t.toSimplexData
        I (I.filter (fun j => a < j ∧ j < b)) a b k hk ha hb
        (fun _ hx => Finset.mem_filter.mp hx) p) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate_differential_eq_blockRhs R B C s t I a b k hk hI ha hb]
  exact dgNerveTensorHomCandidate_differential_eq_survivingSums R B C s t I a b k hk hI ha hb hab

end SerrePositivity.InfinityCategories.Project.DerivedCategories
