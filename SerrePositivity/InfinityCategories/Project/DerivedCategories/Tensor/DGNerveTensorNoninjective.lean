module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveNoninjectiveCutProduct
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorInjectiveNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorEmptyCut
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGTensorElementCalculus
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorEdge
/-!
概要：全次元 tensor 候補の非単射成分は、高次では零、二点では同じ単位に一致する。
方針：選択点の単射性で分けて各切断項を零にし、潰れた二辺は実 tensor 単位と照合する。
規約：HA を仮定しない実 cochain 上の比較。使われ方：全次元候補の退化への自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 非単射な高次添字に沿う同じ tensor 切断項は零となる。 -/
lemma dgNerveTensorCutTerm_pullback_zero {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (α : Fin (m + 1) →o Fin (n + 1))
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (S : Finset (Fin (m + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card) (hIne : I.card ≠ 2)
    (ha : IsLeast (I : Set (Fin (m + 1))) a) (hb : IsGreatest (I : Set (Fin (m + 1))) b)
    (hc : ∀ j ∈ S, j ∈ I ∧ a < j ∧ j < b)
    (hi : ¬ Set.InjOn α (I : Set (Fin (m + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C (s.pullback α) (t.pullback α) I a b S k hk hI ha hb hc = 0 := by
  have hab : a < b := by
    have h := I.min'_lt_max'_of_card (by omega)
    simpa only [← ha.unique (I.isLeast_min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)),
      ← hb.unique (I.isGreatest_max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))] using h
  by_cases hS : S = ∅
  · subst S
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm_empty R B C (s.pullback α) (t.pullback α) I a b k hk hI ha hb hab]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj t α I a b k _ _ _ hk hi hIne]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_zero_right R B C _ _
  · let J : Finset (Fin (m + 1)) := insert a (insert b S)
    by_cases hJ : Set.InjOn α (J : Set (Fin (m + 1)))
    · have hcut := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct_pullback_zero R C t α I a b S hI ha hb hc hJ hi
      unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm
      dsimp only
      rw [hcut, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_zero_right R B C, smul_zero]
    · have haS : a ∉ S := by intro h; exact (lt_irrefl a) (hc a h).2.1
      have hbS : b ∉ S := by intro h; exact (lt_irrefl b) (hc b h).2.2
      have haBS : a ∉ insert b S := by simp [ne_of_lt hab, haS]
      have hcard : J.card = S.card + 2 := by
        dsimp only [J]
        rw [Finset.card_insert_of_notMem haBS, Finset.card_insert_of_notMem hbS]
      have hScard : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
      have hJne : J.card ≠ 2 := by omega
      unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm
      dsimp only
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj s α J a b (-(S.card : ℤ)) _ _ _ _ hJ hJne,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_zero_left R B C, smul_zero]
/-- 非単射な高次添字に沿う全切断和の同じ cochain は零となる。 -/
lemma dgNerveTensorHomCandidate_pullback_zero {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (α : Fin (m + 1) →o Fin (n + 1))
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ)
    (hk : k = 2 - (I.card : ℤ)) (hI : 2 ≤ I.card) (hIne : I.card ≠ 2)
    (ha : IsLeast (I : Set (Fin (m + 1))) a) (hb : IsGreatest (I : Set (Fin (m + 1))) b)
    (hi : ¬ Set.InjOn α (I : Set (Fin (m + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate R B C (s.pullback α) (t.pullback α) I a b k hk hI ha hb = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate
  apply Finset.sum_eq_zero
  intro S _
  exact dgNerveTensorCutTerm_pullback_zero R B C s t α I a b S.val k hk hI hIne ha hb (by
    intro j hj
    exact Finset.mem_filter.mp (Finset.mem_powerset.mp S.property hj)) hi
/-- 高次の非単射成分では、候補の二つの制限方法は同じ零を与える。 -/
lemma dgNerveTensorDataCandidate_noninjective_component {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (α : Fin (m + 1) →o Fin (n + 1))
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hIne : I.card ≠ 2)
    (hi : ¬ Set.InjOn α (I : Set (Fin (m + 1)))) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t).pullback α).hom I a b k hI ha hb hk =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C (s.pullback α) (t.pullback α)).hom I a b k hI ha hb hk := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ α I a b k hI ha hb hk hi hIne]
  exact (dgNerveTensorHomCandidate_pullback_zero R B C s t α I a b k hk hI hIne
    (by rw [ha]; exact I.isLeast_min' _) (by rw [hb]; exact I.isGreatest_max' _) hi).symm
/-- 潰れた実辺の制限は、同じ像の対象の単位に異種等号で一致する。 -/
lemma dgNerveData_pullback_edgeHom_collapsed (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {m n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n) (α : Fin (m + 1) →o Fin (n + 1))
    (a b : Fin (m + 1)) (hab : a < b) (he : α a = α b) :
    HEq ((s.pullback α).edgeHom a b hab) (_root_.SerrePositivity.DifferentialGraded.unitElement R (s.obj (α b))).val := by
  have hi : ¬ Set.InjOn α (({a, b} : Finset (Fin (m + 1))) : Set (Fin (m + 1))) := by
    intro h
    exact (ne_of_lt hab) (h (by simp) (by simp) he)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_collapsed_pair s α {a, b} a b 0
    (by simp [ne_of_lt hab]) _ _ (by simp [ne_of_lt hab]) hi (by simp [ne_of_lt hab])
/-- 潰れた二点成分では、元の二単位の tensor と貼り合わせ先の単位は一致する。 -/
lemma dgNerveTensorDataCandidate_collapsed_pair {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (α : Fin (m + 1) →o Fin (n + 1))
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (h2 : I.card = 2)
    (hi : ¬ Set.InjOn α (I : Set (Fin (m + 1)))) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t).pullback α).hom I a b k hI ha hb hk =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C (s.pullback α) (t.pullback α)).hom I a b k hI ha hb hk := by
  have haI : IsLeast (I : Set (Fin (m + 1))) a := by rw [ha]; exact I.isLeast_min' _
  have hbI : IsGreatest (I : Set (Fin (m + 1))) b := by rw [hb]; exact I.isGreatest_max' _
  have hab : a < b := by
    have h := I.min'_lt_max'_of_card (by omega)
    simpa only [← ha, ← hb] using h
  have he : α a = α b := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.collapse_two hi h2 haI hbI
  have hpair : I = {a, b} := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.eq_pair h2 haI hbI
  have hk0 : k = 0 := by omega
  subst hk0
  subst I
  have hleft := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_collapsed_pair
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t) α {a, b} a b 0 hI ha hb (by simp [ne_of_lt hab]) hi h2
  change _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate R B C (s.pullback α) (t.pullback α)
    {a, b} a b 0 _ _ _ _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate_pair R B C (s.pullback α) (t.pullback α) a b hab]
  apply eq_of_heq
  apply HEq.trans hleft
  apply HEq.symm
  have hTensor := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_heq R B C (n := 0) (n' := 0)
    (x := ((s.obj (α a), t.obj (α a)) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
    (y := ((s.obj (α b), t.obj (α b)) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
    (x' := ((s.obj (α b), t.obj (α b)) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
    (y' := ((s.obj (α b), t.obj (α b)) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
    (congrArg (fun j => ((s.obj j, t.obj j) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C)) he) rfl rfl rfl rfl
    _ _ _ _ (dgNerveData_pullback_edgeHom_collapsed R B s α a b hab he)
    (dgNerveData_pullback_edgeHom_collapsed R C t α a b hab he) (by decide) (by decide)
  exact hTensor.trans
    (heq_of_eq (_root_.SerrePositivity.DifferentialGraded.dgTensor_unitElement R B C (s.obj (α b), t.obj (α b))).symm)
/-- 非単射な全成分について、候補の制限と制限した入力の候補は厳密に一致する。 -/
lemma dgNerveTensorDataCandidate_noninjective_agreement {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B n)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (α : Fin (m + 1) →o Fin (n + 1))
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ))
    (hi : ¬ Set.InjOn α (I : Set (Fin (m + 1)))) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s t).pullback α).hom I a b k hI ha hb hk =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C (s.pullback α) (t.pullback α)).hom I a b k hI ha hb hk := by
  by_cases h2 : I.card = 2
  · exact dgNerveTensorDataCandidate_collapsed_pair R B C s t α I a b k hI ha hb hk h2 hi
  · exact dgNerveTensorDataCandidate_noninjective_component R B C s t α I a b k hI ha hb hk h2 hi
end SerrePositivity.InfinityCategories.Project.DerivedCategories
