module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGTensorTriangleData
/-!
概要：三頂点の全切断和を実 tensor 三角形の同じ cochain へ同定し、HA 微分式を証明する。
方針：内部点の powerset の二項を、空切断と一切断の実 Hom 成分へ戻す。
規約：三次元以上の HA は主張しない。使われ方：全次元 tensor 候補の低次較正。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped BigOperators
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
/-- 三頂点の一切断項は第一三角形 cochain と第二の二辺の合成の tensor。 -/
lemma dgNerveTensorTriangleCut_singleton (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 2) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 2) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s.toSimplexData t.toSimplexData Finset.univ 0 2 {1} (-1)
      (by decide) (by decide) ⟨by simp, fun j _ => Fin.zero_le j⟩
      ⟨by simp, fun j _ => Fin.le_last j⟩ (by
        intro j hj
        have : j = 1 := Finset.mem_singleton.mp hj
        subst j
        decide) =
    _root_.SerrePositivity.DifferentialGraded.dgTensorElement R
      (x := ((s.obj 0, t.obj 0) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (y := ((s.obj 2, t.obj 2) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      s.triangleHom (_root_.SerrePositivity.DifferentialGraded.compose R (t.edgeHom 1 2 (by decide)) (t.edgeHom 0 1 (by decide))
        (by decide : (0 : ℤ) + 0 = 0)) (by decide) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm
  dsimp only
  have hsign : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign (Finset.univ : Finset (Fin 3)) 0 2 {1} = 0 := by decide
  rw [hsign, Int.negOnePow_zero, one_smul,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct_singleton R C t.toSimplexData Finset.univ 0 2 1
      (by decide) _ _ (by simp) (by decide) (by decide)]
  apply eq_of_heq
  refine _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_heq R B C rfl rfl (by decide) (by decide) rfl _ _ _ _ ?_ ?_ _ _
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.triangleHom]
    exact s.toSimplexData.hom_heq_of_indices_degree (by decide) rfl rfl rfl
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom]
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) rfl rfl rfl rfl (by decide) (by decide) _ _ _ _ ?_ ?_ _ _
    · exact t.toSimplexData.hom_heq_of_indices_degree (by decide) rfl rfl (by decide)
    · exact t.toSimplexData.hom_heq_of_indices_degree (by decide) rfl rfl (by decide)
/-- 三頂点の全切断和は、既存の実 tensor 三角形の同じ cochain に一致する。 -/
lemma dgNerveTensorTriangleCandidate_top (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 2) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 2) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate R B C s.toSimplexData t.toSimplexData Finset.univ 0 2 (-1)
      (by decide) (by decide) ⟨by simp, fun j _ => Fin.zero_le j⟩
      ⟨by simp, fun j _ => Fin.le_last j⟩ =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorTriangle R B C s.toTriangle t.toTriangle).homotopy := by
  let I : Finset (Fin 3) := Finset.univ
  let K := I.filter (fun j => (0 : Fin 3) < j ∧ j < 2)
  have hK : K = {1} := by decide
  have hI : 2 ≤ I.card := by decide
  have ha : IsLeast (I : Set (Fin 3)) 0 := ⟨by simp [I], fun j _ => Fin.zero_le j⟩
  have hb : IsGreatest (I : Set (Fin 3)) 2 := ⟨by simp [I], fun j _ => Fin.le_last j⟩
  have hk : (-1 : ℤ) = 2 - (I.card : ℤ) := by decide
  let F (S : Finset (Fin 3)) (hs : S ∈ K.powerset) :
      _root_.SerrePositivity.DifferentialGraded.GradedHom R (D := _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C) (s.obj 0, t.obj 0) (s.obj 2, t.obj 2) (-1) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s.toSimplexData t.toSimplexData I 0 2 S (-1) hk hI ha hb (by
      intro j hj
      exact Finset.mem_filter.mp (Finset.mem_powerset.mp hs hj))
  have h := powersetSingletonSum K 1 hK F
  have he : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate R B C s.toSimplexData t.toSimplexData I 0 2 (-1)
      hk hI ha hb =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s.toSimplexData t.toSimplexData I 0 2 ∅ (-1) hk hI ha hb
        (by simp) +
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s.toSimplexData t.toSimplexData I 0 2 {1} (-1) hk hI ha hb
        (by intro j hj; have : j = 1 := Finset.mem_singleton.mp hj; subst j; decide) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate, F] using! h
  rw [he, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm_empty R B C s.toSimplexData t.toSimplexData I 0 2 (-1)
    hk hI ha hb (by decide)]
  dsimp only [I]
  rw [dgNerveTensorTriangleCut_singleton]
  exact add_comm _ _
/-- 三頂点の候補の全切断和は、同じ辺を持つ HA 微分式を満たす。 -/
lemma dgNerveTensorTriangleCandidate_equation (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 2) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 2) :
    differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate R B C s.toSimplexData t.toSimplexData
      Finset.univ 0 2 (-1) (by decide) (by decide)
      ⟨by simp, fun j _ => Fin.zero_le j⟩ ⟨by simp, fun j _ => Fin.le_last j⟩) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData).rhs
      Finset.univ 0 2 (-1) (by decide) (by decide) (by decide) (by decide) := by
  let d := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData
  have he (a b : Fin 3) (hab : a < b) : d.edgeHom a b hab =
      _root_.SerrePositivity.DifferentialGraded.dgTensorElement R
        (x := ((s.obj a, t.obj a) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
        (y := ((s.obj b, t.obj b) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
        (s.edgeHom a b hab) (t.edgeHom a b hab) (by decide : (0 : ℤ) + 0 = 0) := by
    simpa only [d, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom] using!
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate_pair R B C s.toSimplexData t.toSimplexData a b hab
  rw [dgNerveTensorTriangleCandidate_top, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs_triangle]
  change differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorTriangle R B C s.toTriangle t.toTriangle).homotopy =
    _root_.SerrePositivity.DifferentialGraded.compose R (d.edgeHom 1 2 (by decide)) (d.edgeHom 0 1 (by decide)) (by decide) -
      d.edgeHom 0 2 (by decide)
  rw [he 1 2 (by decide), he 0 1 (by decide), he 0 2 (by decide)]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorTriangle R B C s.toTriangle t.toTriangle).differential_homotopy
end SerrePositivity.InfinityCategories.Project.DerivedCategories
