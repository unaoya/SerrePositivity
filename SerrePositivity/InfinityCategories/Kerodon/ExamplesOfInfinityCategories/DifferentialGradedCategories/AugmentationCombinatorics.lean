module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CompositionCancellation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex

/-! # augmentation に共通する有限切断と dg 係数の計算

DGCommaAug と DGModuleAugmentation で同一だった一般宣言をここに直接移す。
型と証明は DGModuleAugmentation の正本からそのまま保持する。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded

/-- 相一の実内部切断点の有限集合。 -/
def dgModuleAugmentationCutPoints {n : ℕ} (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  I.filter (fun j ↦ a < j ∧ j < b ∧ β j = 1)
/-- 実相切断点の形成は、元の有限集合の点の削除と可換。 -/
lemma dgModuleAugmentationCutPoints_erase {n : ℕ} (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b j : Fin (n + 1)) :
    dgModuleAugmentationCutPoints β (I.erase j) a b =
      (dgModuleAugmentationCutPoints β I a b).erase j :=
  Finset.filter_erase _ _ _
/-- 単調な支持の二重切断和は、支持外から支持内への切断対の寄与に等しい。 -/
lemma dgModuleAugmentationPhase_double_cut_cancel {α : Type*} [LinearOrder α]
    {M : Type*} [AddCommGroup M] (I K : Finset α) (hKI : K ⊆ I)
    (p : α → Prop) [DecidablePred p]
    (hmono : ∀ j ∈ K, ∀ k ∈ K, j < k → p j → p k) (f : α → α → M) :
    (∑ j ∈ K, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • ∑ k ∈ K.filter (j < ·),
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) k • (if p j then f j k else 0)) +
    (∑ k ∈ K, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I k •
      ((2 - ((I.filter (k ≤ ·)).card : ℤ)).negOnePow •
      ∑ j ∈ K.filter (· < k), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ k)) j •
        (if p k then f j k else 0))) =
    ∑ k ∈ K, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I k •
      ((2 - ((I.filter (k ≤ ·)).card : ℤ)).negOnePow •
      ∑ j ∈ K.filter (· < k), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ k)) j •
        (if p k ∧ ¬ p j then f j k else 0)) := by
  simp only [Finset.sum_filter, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hjk : j < k
  · simp only [ite_eq_left hjk]
    by_cases hpj : p j
    · have hpk := hmono j hj k hk hjk hpj
      have hn : ¬ (p k ∧ ¬ p j) := by
        simp only [hpj, not_true_eq_false, and_false, not_false_eq_true]
      simp only [ite_eq_left hpj, ite_eq_left hpk, ite_eq_right hn,
        smul_smul, ← mul_assoc]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign_double_cut I (hKI hk) hjk]
      simp [Units.smul_def]
    · by_cases hpk : p k <;> simp [hpj, hpk]
  · simp only [ite_eq_right hjk, add_zero]
/-- 中央比較三重合成の二つの切断係数は、追加の右次数符号も含めて相殺する。 -/
lemma dgModuleAugmentationImage_double_cut_cancel {α : Type*} [LinearOrder α]
    {M : Type*} [AddCommGroup M] (I : Finset α)
    {j l : α} (hl : l ∈ I) (hjl : j < l) (z : M) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
      ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow • z)) +
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l • (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j • z) = 0 := by
  let q := 2 - ((I.filter (l ≤ ·)).card : ℤ)
  have hsq : q.negOnePow * q.negOnePow = 1 := by
    rw [← Int.negOnePow_add, show q + q = 2 * q by omega, Int.negOnePow_two_mul]
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j * _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l * q.negOnePow =
      -(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l * _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign_double_cut I hl hjl]
    calc
      -(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l * q.negOnePow * _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j) * q.negOnePow =
          -(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l * _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j *
            (q.negOnePow * q.negOnePow)) := by
        rw [neg_mul]
        congr 1
        ac_rfl
      _ = _ := by rw [hsq, mul_one]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l • (q.negOnePow • z)) + _ = 0
  simp only [smul_smul]
  rw [← mul_assoc, hc]
  simp [Units.smul_def]
/-- 単調な切断支持における、中央比較三重合成の全符号和の相殺。 -/
lemma dgModuleAugmentationImage_phase_double_cut_cancel {α : Type*} [LinearOrder α]
    {M : Type*} [AddCommGroup M] (I K : Finset α) (hKI : K ⊆ I)
    (p : α → Prop) [DecidablePred p]
    (hmono : ∀ j ∈ K, ∀ l ∈ K, j < l → p j → p l) (f : α → α → M) :
    (∑ j ∈ K, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • ∑ l ∈ K.filter (j < ·),
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
        ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
        (if p j then f j l else 0))) +
    (∑ l ∈ K, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l • ∑ j ∈ K.filter (· < l),
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j • (if p l ∧ p j then f j l else 0)) = 0 := by
  simp only [Finset.sum_filter, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro l hl
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hjl : j < l
  · simp only [ite_eq_left hjl]
    by_cases hpj : p j
    · have hpl := hmono j hj l hl hjl hpj
      simpa only [ite_eq_left hpj, ite_eq_left (show p l ∧ p j from ⟨hpl, hpj⟩)] using
        dgModuleAugmentationImage_double_cut_cancel I (hKI hl) hjl (f j l)
    · simp [hpj]
  · simp only [ite_eq_right hjl, add_zero]
/-- 相一の切断点は、元の内部点集合を同じ相で制限したもの。 -/
lemma dgModuleAugmentationCutPoints_eq_filter_interior {n : ℕ}
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) :
    dgModuleAugmentationCutPoints β I a b = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (β · = 1) := by
  ext j
  simp only [dgModuleAugmentationCutPoints, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior, Finset.mem_filter]
  tauto
/-- 相一の切断点集合の像を同じ相の切断点集合と同定する。 -/
lemma dgModuleAugmentationCutPoints_image {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (ha : a ∈ I) (hb : b ∈ I)
    (hi : Set.InjOn α (I : Set (Fin (m + 1)))) :
    (dgModuleAugmentationCutPoints (β.comp α) I a b).image α =
      dgModuleAugmentationCutPoints β (I.image α) (α a) (α b) := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
    have hm := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j, hm.1, rfl⟩,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_lt_iff α.monotone hi ha hm.1).mpr hm.2.1,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_lt_iff α.monotone hi hm.1 hb).mpr hm.2.2.1, hm.2.2.2⟩
  · intro hy
    have hm := Finset.mem_filter.mp hy
    rcases Finset.mem_image.mp hm.1 with ⟨j, hj, rfl⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_lt_iff α.monotone hi ha hj).mp hm.2.1,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_lt_iff α.monotone hi hj hb).mp hm.2.2.1, hm.2.2.2⟩, rfl⟩
/-- 左切断の像の濃度は元の同じ左切断の濃度。 -/
lemma dgModuleAugmentationLeftCut_image_card {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (hi : Set.InjOn α (I : Set (Fin (m + 1)))) (j : Fin (m + 1)) (hj : j ∈ I) :
    ((I.image α).filter (· ≤ α j)).card = (I.filter (· ≤ j)).card := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_left α.monotone hi hj]
  exact Finset.card_image_of_injOn (hi.mono (Finset.filter_subset _ _))
/-- 右切断の像の濃度は元の同じ右切断の濃度。 -/
lemma dgModuleAugmentationRightCut_image_card {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (hi : Set.InjOn α (I : Set (Fin (m + 1)))) (j : Fin (m + 1)) (hj : j ∈ I) :
    ((I.image α).filter (α j ≤ ·)).card = (I.filter (j ≤ ·)).card := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_right α.monotone hi hj]
  exact Finset.card_image_of_injOn (hi.mono (Finset.filter_subset _ _))
/-- 共有切断点を持つ左右で単射なら、元の添字集合全体で単射。 -/
lemma dgModuleAugmentationCut_injective_glue {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (j : Fin (m + 1)) (hj : j ∈ I)
    (hL : Set.InjOn α ((I.filter (· ≤ j)) : Set (Fin (m + 1))))
    (hR : Set.InjOn α ((I.filter (j ≤ ·)) : Set (Fin (m + 1)))) :
    Set.InjOn α (I : Set (Fin (m + 1))) := by
  have hcross : ∀ x ∈ I, ∀ y ∈ I, x ≤ j → j ≤ y → α x = α y → x = y := by
    intro x hx y hy hxj hjy he
    have hxj' : α x = α j := le_antisymm (α.monotone hxj)
      (by rw [he]; exact α.monotone hjy)
    have hxj'' : x = j := hL (Finset.mem_filter.mpr ⟨hx, hxj⟩)
      (Finset.mem_filter.mpr ⟨hj, le_refl j⟩) hxj'
    have hjy' : α j = α y := by rw [← hxj'']; exact he
    have hjy'' : j = y := hR (Finset.mem_filter.mpr ⟨hj, le_refl j⟩)
      (Finset.mem_filter.mpr ⟨hy, hjy⟩) hjy'
    exact hxj''.trans hjy''
  intro x hx y hy he
  by_cases hxj : x ≤ j
  · by_cases hyj : y ≤ j
    · exact hL (Finset.mem_filter.mpr ⟨hx, hxj⟩) (Finset.mem_filter.mpr ⟨hy, hyj⟩) he
    · exact hcross x hx y hy hxj (le_of_lt (lt_of_not_ge hyj)) he
  · by_cases hyj : y ≤ j
    · exact (hcross y hy x hx hyj (le_of_lt (lt_of_not_ge hxj)) he.symm).symm
    · exact hR (Finset.mem_filter.mpr ⟨hx, le_of_lt (lt_of_not_ge hxj)⟩)
        (Finset.mem_filter.mpr ⟨hy, le_of_lt (lt_of_not_ge hyj)⟩) he
/-- 正しい全域係数の単射引き戻しは、同じ像の全域係数。 -/
lemma dgSimplexHomOrZero_pullback_of_inj {R : Type u} [CommRing R]
    {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n)
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hi : Set.InjOn α (I : Set (Fin (m + 1)))) :
    (s.pullback α).homOrZero I a b k = s.homOrZero (I.image α) (α a) (α b) k := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq (s.pullback α) I a b k hI ha hb hk,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj s α I a b k hI ha hb hk hi]
  symm
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero_eq s (I.image α) (α a) (α b) k (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hi hI)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone (by rw [ha]; exact I.isLeast_min' _) _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone (by rw [hb]; exact I.isGreatest_max' _) _)
    (by rw [Finset.card_image_of_injOn hi]; exact hk)
/-- 切断点の支持を制限しても、同じ削除・切断混合符号和は相殺する。 -/
lemma dgModuleAugmentation_sum_mixed_cancel_filter
    {α : Type*} [LinearOrder α] {M : Type*} [AddCommGroup M]
    (I K : Finset α) (hKI : K ⊆ I) (p : α → Prop) [DecidablePred p]
    (f : α → α → M) :
    (∑ j ∈ K, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • ∑ l ∈ (K.erase j).filter p,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.erase j) l • f j l) +
    (∑ l ∈ K.filter p, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l • ∑ j ∈ K.filter (l < ·),
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (l ≤ ·)) j • f j l) +
    (∑ l ∈ K.filter p, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
      ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
      ∑ j ∈ K.filter (· < l), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j • f j l)) = 0 := by
  classical
  simpa only [Finset.sum_filter, smul_ite, smul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.sum_mixed_cancel I K hKI (fun j l ↦ if p l then f j l else 0)
/-- 全微分次数を指定した、同じ通常順合成の Leibniz 則。 -/
lemma dgDifferential_compose_of_indices (R : Type u) [CommRing R]
    {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {X Y Z : D} (p q n p' q' n' : ℤ)
    (hpq : p + q = n) (hp : p + 1 = p') (hq : q + 1 = q') (hn : n + 1 = n')
    (g : GradedHom R Y Z q) (f : GradedHom R X Y p) :
    (homObject R D X Z).d n n' (compose R g f hpq) =
    compose R (n := n') ((homObject R D Y Z).d q q' g) f (by omega) +
      q.negOnePow • compose R (n := n') g ((homObject R D X Y).d p p' f) (by omega) := by
  subst p'
  subst q'
  subst n'
  exact differential_compose R g f hpq
end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
