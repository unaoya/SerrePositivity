module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveTripleBoundary
/-!
概要：任意次元の三点 tensor 候補を同じ元の三点 cochain と辺の二項に同定する。
方針：内部点の二つの切断項を比較し、同じ実 tensor 境界式を適用する。
規約：元の二入力が実単体なら全ての三点成分の HA 微分式を満たす。
使われ方：三次元および全次元の tensor 候補の HA 方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped BigOperators
private lemma tripleLeast {n : ℕ} (a b c : Fin (n + 1)) (hab : a < b) (hbc : b < c) :
    IsLeast (({a, b, c} : Finset (Fin (n + 1))) : Set (Fin (n + 1))) a := by
  refine ⟨by simp, ?_⟩
  intro j hj
  change j ∈ ({a, b, c} : Finset (Fin (n + 1))) at hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  · exact le_rfl
  · exact hab.le
  · exact (hab.trans hbc).le
private lemma tripleGreatest {n : ℕ} (a b c : Fin (n + 1)) (hab : a < b) (hbc : b < c) :
    IsGreatest (({a, b, c} : Finset (Fin (n + 1))) : Set (Fin (n + 1))) c := by
  refine ⟨by simp, ?_⟩
  intro j hj
  change j ∈ ({a, b, c} : Finset (Fin (n + 1))) at hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  · exact (hab.trans hbc).le
  · exact hbc.le
  · exact le_rfl
private lemma powersetSingletonSum {α : Type u} {M : Type v} [AddCommMonoid M]
    (K : Finset α) (j : α) (hK : K = {j}) (F : ∀ S : Finset α, S ∈ K.powerset → M) :
    (∑ S : K.powerset, F S.val S.property) =
      F ∅ (by rw [hK]; simp) + F {j} (by rw [hK]; simp) := by
  classical
  let e : K.powerset := ⟨∅, by simp⟩
  let f : K.powerset := ⟨{j}, by rw [hK]; simp⟩
  have hne : e ≠ f := by
    intro h
    have hh := congrArg Subtype.val h
    change (∅ : Finset α) = {j} at hh
    simpa using congrArg Finset.card hh
  apply Finset.sum_eq_add_of_mem e f (Finset.mem_univ _) (Finset.mem_univ _) hne
  intro x _ ⟨he, hf⟩
  have hx : x.val ⊆ {j} := by simpa only [hK] using Finset.mem_powerset.mp x.property
  rcases Finset.subset_singleton_iff.mp hx with h | h
  · exact (he (Subtype.ext h)).elim
  · exact (hf (Subtype.ext h)).elim
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 任意の三点集合の一切断項は同じ三点 cochain と二辺の合成の tensor。 -/
lemma dgNerveTensorTripleCut_singleton {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n)
    (a b c : Fin (n + 1)) (hab : a < b) (hbc : b < c) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s t {a, b, c} a c {b} (-1)
      (by simp [ne_of_lt hab, ne_of_lt hbc, ne_of_lt (hab.trans hbc)])
      (by simp [ne_of_lt hab, ne_of_lt hbc, ne_of_lt (hab.trans hbc)])
      (by
        refine ⟨by simp, ?_⟩
        intro j hj
        change j ∈ ({a, b, c} : Finset (Fin (n + 1))) at hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl <;> omega) (by
        refine ⟨by simp, ?_⟩
        intro j hj
        change j ∈ ({a, b, c} : Finset (Fin (n + 1))) at hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl <;> omega) (by
        intro j hj
        have : j = b := Finset.mem_singleton.mp hj
        subst j
        exact ⟨by simp, hab, hbc⟩) =
    _root_.SerrePositivity.DifferentialGraded.dgTensorElement R
      (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (y := ((s.obj c, t.obj c) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (s.tripleHom a b c hab hbc)
      (_root_.SerrePositivity.DifferentialGraded.compose R (n := 0) (t.edgeHom b c hbc) (t.edgeHom a b hab) (by decide)) (by decide) := by
  have he : (({a, b, c} : Finset (Fin (n + 1))).erase a).erase c = {b} := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    have hba := ne_of_gt hab
    have hbc' := ne_of_lt hbc
    aesop
  have hsign : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign {a, b, c} a c {b} = 0 := by
    simpa only [he] using _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign_all {a, b, c} a c
  have hl : ({a, b, c} : Finset (Fin (n + 1))).filter (· ≤ b) = {a, b} := by
    simp [Finset.filter_insert, Finset.filter_singleton, hab.le, not_le_of_gt hbc]
  have hr : ({a, b, c} : Finset (Fin (n + 1))).filter (b ≤ ·) = {b, c} := by
    simp [Finset.filter_insert, Finset.filter_singleton, hbc.le, not_le_of_gt hab]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm
  dsimp only
  rw [hsign, Int.negOnePow_zero, one_smul,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct_singleton R C t {a, b, c} a c b _ _ _ (by simp) hab hbc]
  apply eq_of_heq
  refine _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_heq R B C rfl rfl (by simp) (by simp [ne_of_lt hab,
    ne_of_lt hbc, ne_of_lt (hab.trans hbc)]) rfl _ _ _ _ ?_ ?_ _ _
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom]
    exact s.hom_heq_of_indices_degree (by ext j; simp [or_comm]) rfl rfl (by simp)
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom]
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) rfl rfl rfl
      (by simp [hl, ne_of_lt hab]) (by simp [hr, ne_of_lt hbc]) (by
        simp [ne_of_lt hab, ne_of_lt hbc, ne_of_lt (hab.trans hbc)]) _ _ _ _ ?_ ?_ _ _
    · exact t.hom_heq_of_indices_degree hr rfl rfl (by simp [hr, ne_of_lt hbc])
    · exact t.hom_heq_of_indices_degree hl rfl rfl (by simp [hl, ne_of_lt hab])
/-- 任意次元の三点候補は、元の実 cochain の二つの tensor 項の和。 -/
lemma dgNerveTensorHomCandidate_triple {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n)
    (a b c : Fin (n + 1)) (hab : a < b) (hbc : b < c) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate R B C s t {a, b, c} a c (-1)
      (by simp [ne_of_lt hab, ne_of_lt hbc, ne_of_lt (hab.trans hbc)])
      (by simp [ne_of_lt hab, ne_of_lt hbc, ne_of_lt (hab.trans hbc)])
      (by
        refine ⟨by simp, ?_⟩
        intro j hj
        change j ∈ ({a, b, c} : Finset (Fin (n + 1))) at hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl <;> omega) (by
        refine ⟨by simp, ?_⟩
        intro j hj
        change j ∈ ({a, b, c} : Finset (Fin (n + 1))) at hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl <;> omega) =
    _root_.SerrePositivity.DifferentialGraded.dgTensorElement R
      (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (y := ((s.obj c, t.obj c) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (s.edgeHom a c (hab.trans hbc)) (t.tripleHom a b c hab hbc) (by decide) +
    _root_.SerrePositivity.DifferentialGraded.dgTensorElement R
      (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (y := ((s.obj c, t.obj c) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (s.tripleHom a b c hab hbc)
      (_root_.SerrePositivity.DifferentialGraded.compose R (n := 0) (t.edgeHom b c hbc) (t.edgeHom a b hab) (by decide)) (by decide) := by
  let I : Finset (Fin (n + 1)) := {a, b, c}
  let K := I.filter (fun j => a < j ∧ j < c)
  have hK : K = {b} := by
    simp [K, I, Finset.filter_insert, Finset.filter_singleton, hab, hbc]
  have hI : 2 ≤ I.card := by
    simp [I, ne_of_lt hab, ne_of_lt hbc, ne_of_lt (hab.trans hbc)]
  have hk : (-1 : ℤ) = 2 - (I.card : ℤ) := by
    simp [I, ne_of_lt hab, ne_of_lt hbc, ne_of_lt (hab.trans hbc)]
  let F (S : Finset (Fin (n + 1))) (hs : S ∈ K.powerset) :
      _root_.SerrePositivity.DifferentialGraded.GradedHom R (D := _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C) (s.obj a, t.obj a) (s.obj c, t.obj c) (-1) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s t I a c S (-1) hk hI
      (tripleLeast a b c hab hbc) (tripleGreatest a b c hab hbc) (by
        intro j hj
        exact Finset.mem_filter.mp (Finset.mem_powerset.mp hs hj))
  have h := powersetSingletonSum K b hK F
  have he : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate R B C s t I a c (-1) hk hI
      (tripleLeast a b c hab hbc) (tripleGreatest a b c hab hbc) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s t I a c ∅ (-1) hk hI
      (tripleLeast a b c hab hbc) (tripleGreatest a b c hab hbc) (by simp) +
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s t I a c {b} (-1) hk hI
      (tripleLeast a b c hab hbc) (tripleGreatest a b c hab hbc) (by
        intro j hj; have : j = b := Finset.mem_singleton.mp hj; subst j
        exact ⟨by simp [I], hab, hbc⟩) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate, F] using! h
  rw [he, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm_empty R B C s t I a c (-1) hk hI _ _ (hab.trans hbc)]
  dsimp only [I]
  rw [dgNerveTensorTripleCut_singleton]
  rfl
/-- 全次元候補の辺は元の同じ二辺の実 tensor。 -/
lemma dgNerveTensorDataCandidate_edgeHom {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (a c : Fin (n + 1)) (hac : a < c) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t).edgeHom a c hac =
    _root_.SerrePositivity.DifferentialGraded.dgTensorElement R
      (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (y := ((s.obj c, t.obj c) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (s.edgeHom a c hac) (t.edgeHom a c hac) (by decide : (0 : ℤ) + 0 = 0) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom] using!
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate_pair R B C s t a c hac
/-- 全次元候補の三点成分は元の同じ cochain と辺の二項に一致する。 -/
lemma dgNerveTensorDataCandidate_tripleHom {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (a b c : Fin (n + 1)) (hab : a < b) (hbc : b < c) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t).tripleHom a b c hab hbc =
    _root_.SerrePositivity.DifferentialGraded.dgTensorElement R
      (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (y := ((s.obj c, t.obj c) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (s.edgeHom a c (hab.trans hbc)) (t.tripleHom a b c hab hbc) (by decide) +
    _root_.SerrePositivity.DifferentialGraded.dgTensorElement R
      (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (y := ((s.obj c, t.obj c) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (s.tripleHom a b c hab hbc)
      (_root_.SerrePositivity.DifferentialGraded.compose R (n := 0) (t.edgeHom b c hbc) (t.edgeHom a b hab) (by decide)) (by decide) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom] using!
    dgNerveTensorHomCandidate_triple R B C s t a b c hab hbc
/-- 二つの実単体から作った候補の全ての三点成分は HA 微分式を満たす。 -/
lemma dgNerveTensorDataCandidate_triple_differential {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B n)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C n) (a b c : Fin (n + 1)) (hab : a < b) (hbc : b < c) :
    differential R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData).tripleHom
      a b c hab hbc) =
    _root_.SerrePositivity.DifferentialGraded.compose R (n := 0)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData).edgeHom b c hbc)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData).edgeHom a b hab)
      (by decide) -
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData).edgeHom
        a c (hab.trans hbc) := by
  rw [dgNerveTensorDataCandidate_tripleHom, dgNerveTensorDataCandidate_edgeHom,
    dgNerveTensorDataCandidate_edgeHom, dgNerveTensorDataCandidate_edgeHom,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_composeZero]
  have hg : _root_.SerrePositivity.DifferentialGraded.differential R
      (_root_.SerrePositivity.DifferentialGraded.compose R (n := 0) (t.edgeHom b c hbc) (t.edgeHom a b hab) (by decide)) = 0 := by
    rw [_root_.SerrePositivity.DifferentialGraded.differential_compose, t.differential_edgeHom b c hbc, t.differential_edgeHom a b hab,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, add_zero]
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorBoundary R B C
    ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C)
    ((s.obj c, t.obj c) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C)
    (s.edgeHom a c (hab.trans hbc))
    (_root_.SerrePositivity.DifferentialGraded.compose R (n := 0) (s.edgeHom b c hbc) (s.edgeHom a b hab) (by decide))
    (t.edgeHom a c (hab.trans hbc))
    (_root_.SerrePositivity.DifferentialGraded.compose R (n := 0) (t.edgeHom b c hbc) (t.edgeHom a b hab) (by decide))
    (s.toSimplexData.tripleHom a b c hab hbc) (t.toSimplexData.tripleHom a b c hab hbc)
    (s.differential_edgeHom a c (hab.trans hbc)) hg
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTripleHom_differential R B s a b c hab hbc)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTripleHom_differential R C t a b c hab hbc)
  apply Eq.trans ?_ h
  exact congrArg (_root_.SerrePositivity.DifferentialGraded.differential R) (add_comm _ _)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
