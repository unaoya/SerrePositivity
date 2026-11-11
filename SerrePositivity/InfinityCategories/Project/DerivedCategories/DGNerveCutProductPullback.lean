module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutImageIndex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveListCutLow
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutProduct
/-!
概要：任意次元の実切断合成は、単射に沿う入力の制限と切断添字の像で一致する。
方針：昇順列で帰納し、実 Hom の単射制限・左右切断の像・同じ合成の異種等号を使う。
規約：指定次数の実 cochain と有限集合版の次数比較を保持する。使われ方：tensor 候補の全次元自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 全次元の昇順切断合成は、単射に沿う制限と同じ像の合成で厳密に一致する。 -/
lemma dgNerveListCutProduct_pullback {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (L : List (Fin (m + 1)))
    (k : ℤ) (hk : k = 2 - (I.card : ℤ) + (L.length : ℤ))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (m + 1))) a)
    (hb : IsGreatest (I : Set (Fin (m + 1))) b) (ho : L.Pairwise (· < ·))
    (hc : ∀ j ∈ L, j ∈ I ∧ a < j ∧ j < b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D (s.pullback α) I a b L k hk hI ha hb ho hc =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct R D s (I.image α) (α a) (α b) (L.map α) k
        (by rw [Finset.card_image_of_injOn hα.injOn, List.length_map]; exact hk)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hα.injOn hI) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutImageLeast α I a ha)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutImageGreatest α I b hb) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutImagePairwise α hα L ho)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutImageInterior α hα I a b L hc) := by
  induction L generalizing I a b k with
  | nil =>
    simp only [List.map_nil]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct]
    dsimp only [List.casesOn]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct]
    dsimp only [List.map_nil, List.casesOn]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj s α I a b k _ _ _ _ hα.injOn]
  | cons j L ih =>
    have hj := hc j (by simp)
    have hp := List.pairwise_cons.mp ho
    have hl : (I.filter (· ≤ j)).image α = (I.image α).filter (· ≤ α j) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_left α.monotone hα.injOn hj.1
    have hr : (I.filter (j ≤ ·)).image α = (I.image α).filter (α j ≤ ·) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_right α.monotone hα.injOn hj.1
    have hcl : ((I.image α).filter (· ≤ α j)).card = (I.filter (· ≤ j)).card := by
      rw [← hl, Finset.card_image_of_injOn hα.injOn]
    have hcr : ((I.image α).filter (α j ≤ ·)).card = (I.filter (j ≤ ·)).card := by
      rw [← hr, Finset.card_image_of_injOn hα.injOn]
    conv_lhs => rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct]; dsimp only [List.casesOn]
    conv_rhs =>
      simp only [List.map_cons]
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct]
      dsimp only [List.casesOn]
    apply eq_of_heq
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) rfl rfl rfl (by rw [hcl])
      (by rw [hcr, List.length_map]) rfl _ _ _ _ ?_ ?_ _ _
    · let Q := I.filter (j ≤ ·)
      have hQ : 2 ≤ Q.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hj.1 hb.1 hj.2.2
      have hjQ : IsLeast (Q : Set (Fin (m + 1))) j :=
        ⟨Finset.mem_filter.mpr ⟨hj.1, le_rfl⟩, fun _ hz => (Finset.mem_filter.mp hz).2⟩
      have hbQ : IsGreatest (Q : Set (Fin (m + 1))) b :=
        ⟨Finset.mem_filter.mpr ⟨hb.1, hj.2.2.le⟩,
          fun _ hz => hb.2 (Finset.mem_filter.mp hz).1⟩
      have ht : ∀ z ∈ L, z ∈ Q ∧ j < z ∧ z < b := by
        intro z hz
        have hzI := hc z (List.mem_cons_of_mem j hz)
        have hjz := hp.1 z hz
        exact ⟨Finset.mem_filter.mpr ⟨hzI.1, hjz.le⟩, hjz, hzI.2.2⟩
      have hrec := ih Q j b (2 - (Q.card : ℤ) + (L.length : ℤ)) rfl hQ hjQ hbQ hp.2 ht
      apply HEq.trans (heq_of_eq hrec)
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_heq R D s hr rfl rfl rfl (by
        dsimp only [Q]
        rw [hcr, List.length_map])
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj s α (I.filter (· ≤ j)) a j
        (2 - ((I.filter (· ≤ j)).card : ℤ)) _ _ _ rfl hα.injOn]
      exact s.hom_heq_of_indices_degree hl rfl rfl (by rw [hcl])
/-- 単射な単調写像の像を昇順に並べることは、元の昇順列を写すことと一致する。 -/
lemma dgNerveCutImage_sort {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (hα : Function.Injective α) (S : Finset (Fin (m + 1))) :
    (S.image α).sort (· ≤ ·) = (S.sort (· ≤ ·)).map α := by
  apply (Finset.sortedLT_sort (S.image α)).eq_of_mem_iff
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutImagePairwise α hα (S.sort (· ≤ ·)) (Finset.sortedLT_sort S).pairwise).sortedLT
  intro j
  simp
/-- 有限切断集合による同じ実合成は、単射に沿う像の合成と次数を保って一致する。 -/
lemma dgNerveCutProduct_pullback_heq {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (S : Finset (Fin (m + 1)))
    (hI : 2 ≤ I.card) (ha : IsLeast (I : Set (Fin (m + 1))) a)
    (hb : IsGreatest (I : Set (Fin (m + 1))) b)
    (hc : ∀ j ∈ S, j ∈ I ∧ a < j ∧ j < b) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct R D (s.pullback α) I a b S hI ha hb hc)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct R D s (I.image α) (α a) (α b) (S.image α)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hα.injOn hI) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutImageLeast α I a ha)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutImageGreatest α I b hb) (by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
          have h := hc x hx
          have hs := α.monotone.strictMono_of_injective hα
          exact ⟨Finset.mem_image.mpr ⟨x, h.1, rfl⟩, hs h.2.1, hs h.2.2⟩)) := by
  have h := dgNerveListCutProduct_pullback R D s α hα I a b (S.sort (· ≤ ·))
    (2 - (I.card : ℤ) + (S.card : ℤ)) (by rw [Finset.length_sort]) hI ha hb
    (Finset.sortedLT_sort S).pairwise (by
      intro j hj
      exact hc j ((Finset.mem_sort (· ≤ ·)).mp hj))
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct
  apply HEq.trans (heq_of_eq h)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_heq R D s rfl rfl rfl (dgNerveCutImage_sort α hα S).symm
    (by simp only [Finset.card_image_of_injOn hα.injOn])
end SerrePositivity.InfinityCategories.Project.DerivedCategories
