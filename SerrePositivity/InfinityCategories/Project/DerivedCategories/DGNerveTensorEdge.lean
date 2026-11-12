module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGTensorElementCalculus
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveTensorCandidate
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveTensorEmptyCut
/-!
概要：全次元 tensor 候補の辺を元の二つの辺の tensor と同定し、閉性を証明する。
方針：二点集合には内部切断がないため、有限和を空切断の一項へ戻す。
規約：高次 HA 方程式は主張しない。使われ方：直積から tensor nerve への構成の辺成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped BigOperators
private lemma finsetPowersetSumEmpty {α : Type u} {M : Type v} [AddCommMonoid M]
    (K : Finset α) (hK : K = ∅) (F : ∀ S : Finset α, S ∈ K.powerset → M) :
    (∑ S : K.powerset, F S.val S.property) = F ∅ (by rw [hK]; simp) := by
  classical
  subst K
  simp
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 二点集合の候補成分は同じ二辺の実 tensor である。 -/
lemma dgNerveTensorHomCandidate_pair {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n)
    (a b : Fin (n + 1)) (hab : a < b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate R B C s t {a, b} a b 0
      (by simp [ne_of_lt hab]) (by simp [ne_of_lt hab])
      (by simpa [min_eq_left hab.le] using (isLeast_pair (a := a) (b := b)))
      (by simpa [max_eq_right hab.le] using (isGreatest_pair (a := a) (b := b))) =
    _root_.SerrePositivity.DifferentialGraded.dgTensorElement R
      (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (y := ((s.obj b, t.obj b) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (s.edgeHom a b hab) (t.edgeHom a b hab) (by decide : (0 : ℤ) + 0 = 0) := by
  have hi : ({a, b} : Finset (Fin (n + 1))).filter (fun j => a < j ∧ j < b) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro j hj hh
    rcases Finset.mem_insert.mp hj with h | h
    · subst j
      exact (lt_irrefl a) hh.1
    · have : j = b := Finset.mem_singleton.mp h
      subst j
      exact (lt_irrefl b) hh.2
  have hk : (0 : ℤ) = 2 - (({a, b} : Finset (Fin (n + 1))).card : ℤ) := by
    simp [ne_of_lt hab]
  have hI : 2 ≤ ({a, b} : Finset (Fin (n + 1))).card := by simp [ne_of_lt hab]
  have ha : IsLeast (({a, b} : Finset (Fin (n + 1))) : Set (Fin (n + 1))) a := by
    simpa [min_eq_left hab.le] using (isLeast_pair (a := a) (b := b))
  have hb : IsGreatest (({a, b} : Finset (Fin (n + 1))) : Set (Fin (n + 1))) b := by
    simpa [max_eq_right hab.le] using (isGreatest_pair (a := a) (b := b))
  let K := ({a, b} : Finset (Fin (n + 1))).filter (fun j => a < j ∧ j < b)
  let F (S : Finset (Fin (n + 1))) (hs : S ∈ K.powerset) :
      _root_.SerrePositivity.DifferentialGraded.GradedHom R (D := _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C) (s.obj a, t.obj a) (s.obj b, t.obj b) 0 :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s t {a, b} a b S 0 hk hI ha hb (by
      intro j hj
      obtain ⟨hjI, haj, hjb⟩ := Finset.mem_filter.mp (Finset.mem_powerset.mp hs hj)
      exact ⟨hjI, haj, hjb⟩)
  have h := finsetPowersetSumEmpty K hi F
  have he : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate R B C s t {a, b} a b 0 hk hI ha hb =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s t {a, b} a b ∅ 0 hk hI ha hb (by simp) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate, F] using! h
  rw [he, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm_empty R B C s t {a, b} a b 0 hk hI ha hb hab]
  rfl
/-- 二つの実単体から作った全次元候補の各辺は閉じている。 -/
lemma dgNerveTensorDataCandidate_edge_closed {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C n)
    (a b : Fin (n + 1)) (hab : a < b) :
    differential R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData).edgeHom
      a b hab) = 0 := by
  have h := dgNerveTensorHomCandidate_pair R B C s.toSimplexData t.toSimplexData a b hab
  have he : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData).edgeHom a b hab =
      _root_.SerrePositivity.DifferentialGraded.dgTensorElement R
        (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
        (y := ((s.obj b, t.obj b) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
        (s.edgeHom a b hab) (t.edgeHom a b hab) (by decide : (0 : ℤ) + 0 = 0) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom] using! h
  rw [he]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_closed R B C
    (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
    (y := ((s.obj b, t.obj b) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
    (s.edgeHom a b hab) (t.edgeHom a b hab)
    (s.differential_edgeHom a b hab) (t.differential_edgeHom a b hab)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
