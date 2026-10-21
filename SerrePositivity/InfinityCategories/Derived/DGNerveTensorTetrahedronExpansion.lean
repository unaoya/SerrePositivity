module
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorTetrahedronSingleCuts
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorTetrahedronExtremeCuts
/-!
概要：四頂点の tensor 候補の全切断和を、元の実 Hom 成分の符号付き四項へ展開する。
方針：内部点の powerset の全四元を列挙し、それぞれ同じ実切断項へ同定する。
規約：全 HA 方程式とは区別する。使われ方：三次元 HA の Leibniz 展開と符号照合。
-/
@[expose] public section
noncomputable section
universe u
open scoped BigOperators
private lemma powersetPairSum {M : Type u} [AddCommMonoid M]
    (K : Finset (Fin 4)) (hK : K = {1, 2})
    (F : ∀ S : Finset (Fin 4), S ∈ K.powerset → M) :
    (∑ S : K.powerset, F S.val S.property) =
      F ∅ (by simp) + F {1} (by rw [hK]; simp) +
      F {2} (by rw [hK]; simp) + F {1, 2} (by rw [hK]; simp) := by
  classical
  let e : K.powerset := ⟨∅, by simp⟩
  let f : K.powerset := ⟨{1}, by rw [hK]; simp⟩
  let g : K.powerset := ⟨{2}, by rw [hK]; simp⟩
  let h : K.powerset := ⟨{1, 2}, by rw [hK]; simp⟩
  have hall : (Finset.univ : Finset K.powerset) = {e, f, g, h} := by
    ext x
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    have hx : x.val ⊆ {1, 2} := by simpa only [hK] using Finset.mem_powerset.mp x.property
    by_cases h1 : 1 ∈ x.val <;> by_cases h2 : 2 ∈ x.val
    · right; right; right
      apply Subtype.ext
      apply Finset.Subset.antisymm hx
      exact Finset.insert_subset h1 (Finset.singleton_subset_iff.mpr h2)
    · right; left
      apply Subtype.ext
      ext j
      constructor
      · intro hj
        rcases Finset.mem_insert.mp (hx hj) with hj1 | hj2
        · exact Finset.mem_singleton.mpr hj1
        · exact (h2 (Finset.mem_singleton.mp hj2 ▸ hj)).elim
      · intro hj; exact Finset.mem_singleton.mp hj ▸ h1
    · right; right; left
      apply Subtype.ext
      ext j
      constructor
      · intro hj
        rcases Finset.mem_insert.mp (hx hj) with hj1 | hj2
        · exact (h1 (hj1 ▸ hj)).elim
        · exact hj2
      · intro hj; exact Finset.mem_singleton.mp hj ▸ h2
    · left
      apply Subtype.ext
      change x.val = ∅
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      rcases Finset.mem_insert.mp (hx hj) with hj1 | hj2
      · exact h1 (hj1 ▸ hj)
      · exact h2 (Finset.mem_singleton.mp hj2 ▸ hj)
  change (∑ x ∈ (Finset.univ : Finset K.powerset), F x.val x.property) = _
  rw [hall]
  rw [Finset.sum_insert (by
      simp only [e, f, g, h, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq]
      decide), Finset.sum_insert (by
      simp only [f, g, h, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq]
      decide), Finset.sum_insert (by
      simp only [g, h, Finset.mem_singleton, Subtype.mk.injEq]
      decide), Finset.sum_singleton]
  change F ∅ _ + (F {1} _ + (F {2} _ + F {1, 2} _)) = _
  abel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
/-- 全切断和の四頂点の最高成分を、元の cochain の同じ符号付き四項で表す。 -/
lemma dgNerveTensorTetrahedronCandidate_top (s : SimplexData R B 3) (t : SimplexData R C 3) :
    dgNerveTensorHomCandidate R B C s t Finset.univ 0 3 (-2) (by decide) (by decide)
      ⟨by simp, fun j _ => Fin.zero_le j⟩ ⟨by simp, fun j _ => Fin.le_last j⟩ =
      dgTensorElement R
        (x := ((s.obj 0, t.obj 0) : DGTensorCategory R B C))
        (y := ((s.obj 3, t.obj 3) : DGTensorCategory R B C))
        (s.edgeHom 0 3 (by decide)) (dgNerveTetrahedronHom R C t) (by decide) -
      dgTensorElement R
        (x := ((s.obj 0, t.obj 0) : DGTensorCategory R B C))
        (y := ((s.obj 3, t.obj 3) : DGTensorCategory R B C))
        (s.tripleHom 0 1 3 (by decide) (by decide))
        (compose R (n := -1) (t.tripleHom 1 2 3 (by decide) (by decide))
          (t.edgeHom 0 1 (by decide)) (by decide)) (by decide) +
      dgTensorElement R
        (x := ((s.obj 0, t.obj 0) : DGTensorCategory R B C))
        (y := ((s.obj 3, t.obj 3) : DGTensorCategory R B C))
        (s.tripleHom 0 2 3 (by decide) (by decide))
        (compose R (n := -1) (t.edgeHom 2 3 (by decide))
          (t.tripleHom 0 1 2 (by decide) (by decide)) (by decide)) (by decide) +
      dgTensorElement R
        (x := ((s.obj 0, t.obj 0) : DGTensorCategory R B C))
        (y := ((s.obj 3, t.obj 3) : DGTensorCategory R B C))
        (dgNerveTetrahedronHom R B s)
        (compose R (n := 0)
          (compose R (n := 0) (t.edgeHom 2 3 (by decide)) (t.edgeHom 1 2 (by decide)) (by decide))
          (t.edgeHom 0 1 (by decide)) (by decide)) (by decide) := by
  let K := (Finset.univ : Finset (Fin 4)).filter (fun j => (0 : Fin 4) < j ∧ j < 3)
  have hK : K = {1, 2} := by decide
  have ha : IsLeast ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)) 0 :=
    ⟨by simp, fun j _ => Fin.zero_le j⟩
  have hb : IsGreatest ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)) 3 :=
    ⟨by simp, fun j _ => Fin.le_last j⟩
  let F (S : Finset (Fin 4)) (hs : S ∈ K.powerset) :
      GradedHom R (D := DGTensorCategory R B C) (s.obj 0, t.obj 0) (s.obj 3, t.obj 3) (-2) :=
    dgNerveTensorCutTerm R B C s t Finset.univ 0 3 S (-2) (by decide) (by decide) ha hb (by
      intro j hj
      exact Finset.mem_filter.mp (Finset.mem_powerset.mp hs hj))
  have h := powersetPairSum K hK F
  have he : dgNerveTensorHomCandidate R B C s t Finset.univ 0 3 (-2)
      (by decide) (by decide) ha hb =
      dgNerveTensorCutTerm R B C s t Finset.univ 0 3 ∅ (-2)
        (by decide) (by decide) ha hb (by decide) +
      dgNerveTensorCutTerm R B C s t Finset.univ 0 3 {1} (-2)
        (by decide) (by decide) ha hb (by decide) +
      dgNerveTensorCutTerm R B C s t Finset.univ 0 3 {2} (-2)
        (by decide) (by decide) ha hb (by decide) +
      dgNerveTensorCutTerm R B C s t Finset.univ 0 3 {1, 2} (-2)
        (by decide) (by decide) ha hb (by decide) := by
    simpa only [dgNerveTensorHomCandidate, F] using! h
  rw [he, dgNerveTensorTetrahedronCut_empty, dgNerveTensorTetrahedronCut_first,
    dgNerveTensorTetrahedronCut_second, dgNerveTensorTetrahedronCut_all, sub_eq_add_neg]
end SerrePositivity.InfinityCategories
