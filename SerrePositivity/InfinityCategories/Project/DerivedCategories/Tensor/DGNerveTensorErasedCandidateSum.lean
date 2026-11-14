module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveCutVertexReindex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorContributionsSum
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorCandidate
/-!
概要：削除の残存和を同じ削除後候補の符号付き和へ同定する。
方針：同じ頂点ごとの切断集合を実添字同値で移し、線形性を使う。
規約：元の全次数の cochain を使う。使われ方：候補自身の全 HA 右辺の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped BigOperators
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 元の残存和と候補の境界成分の比較。 -/
def dgNerveTensorCandidateDeletionTerm {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (j : (I.filter (fun x => a < x ∧ x < b))) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (D := _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C) (s.obj a, t.obj a) (s.obj b, t.obj b) (k + 1) := by
  have hj := Finset.mem_filter.mp j.property
  have hE : 2 ≤ (I.erase j.val).card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two ha.1 hb.1 hj.2.1 hj.2.2
  have haE : IsLeast ((I.erase j.val) : Set (Fin (n + 1))) a :=
    ⟨Finset.mem_erase.mpr ⟨ne_of_lt hj.2.1, ha.1⟩,
      fun _ hx => ha.2 (Finset.mem_erase.mp hx).2⟩
  have hbE : IsGreatest ((I.erase j.val) : Set (Fin (n + 1))) b :=
    ⟨Finset.mem_erase.mpr ⟨Ne.symm (ne_of_lt hj.2.2), hb.1⟩,
      fun _ hx => hb.2 (Finset.mem_erase.mp hx).2⟩
  exact ((I.filter (j.val < ·)).card : ℤ).negOnePow •
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate R B C s t (I.erase j.val) a b (k + 1)
      (by have hcard := Finset.card_erase_add_one hj.1; omega) hE haE hbE
/-- 元の残存和と候補の境界成分の比較。 -/
lemma dgNerveTensorErasedCutSummand_vertex_sum {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b)
    (j : (I.filter (fun x => a < x ∧ x < b))) :
    (∑ U : {U : Finset (Fin (n + 1)) // U ⊆ (I.filter (fun x => a < x ∧ x < b)).erase j.val},
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorErasedCutSummand R B C s t I (I.filter (fun x => a < x ∧ x < b))
        a b k hk ha hb (fun _ hx => Finset.mem_filter.mp hx)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutInsertionVertexEquiv _).symm ⟨j, U⟩)) =
      dgNerveTensorCandidateDeletionTerm R B C s t I a b k hk ha hb j := by
  let T := I.filter (fun x => a < x ∧ x < b)
  let E := (I.erase j.val).filter (fun x => a < x ∧ x < b)
  have he : E = T.erase j.val := by
    ext x
    simp only [E, T, Finset.mem_filter, Finset.mem_erase]
    tauto
  let e : {U : Finset (Fin (n + 1)) // U ⊆ T.erase j.val} ≃ E.powerset :=
    { toFun := fun U => ⟨U.val, Finset.mem_powerset.mpr (by rw [he]; exact U.property)⟩
      invFun := fun U => ⟨U.val, by rw [← he]; exact Finset.mem_powerset.mp U.property⟩
      left_inv := fun U => by apply Subtype.ext; rfl
      right_inv := fun U => by apply Subtype.ext; rfl }
  unfold dgNerveTensorCandidateDeletionTerm _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate
  rw [Finset.smul_sum]
  have hj := Finset.mem_filter.mp j.property
  have hE : 2 ≤ (I.erase j.val).card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two ha.1 hb.1 hj.2.1 hj.2.2
  have haE : IsLeast ((I.erase j.val) : Set (Fin (n + 1))) a :=
    ⟨Finset.mem_erase.mpr ⟨ne_of_lt hj.2.1, ha.1⟩,
      fun _ hx => ha.2 (Finset.mem_erase.mp hx).2⟩
  have hbE : IsGreatest ((I.erase j.val) : Set (Fin (n + 1))) b :=
    ⟨Finset.mem_erase.mpr ⟨Ne.symm (ne_of_lt hj.2.2), hb.1⟩,
      fun _ hx => hb.2 (Finset.mem_erase.mp hx).2⟩
  let f := fun U : E.powerset => ((I.filter (j.val < ·)).card : ℤ).negOnePow •
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s t (I.erase j.val) a b U.val (k + 1)
      (by have hcard := Finset.card_erase_add_one hj.1; omega) hE haE hbE
      (fun x hx => Finset.mem_filter.mp (Finset.mem_powerset.mp U.property hx))
  change (∑ U, f (e U)) = ∑ U, f U
  exact Equiv.sum_comp e f
/-- 元の残存和と候補の境界成分の比較。 -/
lemma dgNerveTensorErasedCutSummand_sum {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (ha : IsLeast (I : Set (Fin (n + 1))) a) (hb : IsGreatest (I : Set (Fin (n + 1))) b) :
    (∑ p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutInsertionIndex (I.filter (fun x => a < x ∧ x < b)),
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorErasedCutSummand R B C s t I (I.filter (fun x => a < x ∧ x < b))
        a b k hk ha hb (fun _ hx => Finset.mem_filter.mp hx) p) =
      ∑ j : (I.filter (fun x => a < x ∧ x < b)),
        dgNerveTensorCandidateDeletionTerm R B C s t I a b k hk ha hb j := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutInsertionVertex_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact dgNerveTensorErasedCutSummand_vertex_sum R B C s t I a b k hk ha hb j
end SerrePositivity.InfinityCategories.Project.DerivedCategories
