module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationCutBoundary
/-!
概要：実切断の左右の削除を同じ合成へ同定し、線形境界を削除和へ移す。
方針：片側の切断集合の不変性と濃度の変化、同じ比較成分の次数輸送を使う。
規約：元の実係数を保持する。使われ方：augmentation 補正の全削除和の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  {n : ℕ} (s : SimplexData R (DGModuleFunctorResolutionObject R C E F) n)
/-- 右側の一点削除後の実切断は、同じ右削除係数と左像の合成。 -/
lemma dgModuleAugmentationHomotopyCut_erase_right
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (j l : Fin (n + 1)) (hj : j ∈ I) (hlj : l < j)
    (hsum : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) = k) :
    dgModuleAugmentationHomotopyCut R C E F s (I.erase j) a b (k + 1) l =
    compose R (x := (s.obj a).replacement.val) (y := (s.obj l).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (dgModuleAugmentationHomotopyAt R C E F (s.obj l) (s.obj b)
        (2 - ((I.filter (l ≤ ·)).card : ℤ) + 1)
        (2 - ((I.filter (l ≤ ·)).card : ℤ)) (by omega)
        (s.homOrZero ((I.filter (l ≤ ·)).erase j) l b
          (2 - ((I.filter (l ≤ ·)).card : ℤ) + 1)))
      (((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
        (s.homOrZero (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ))))
      (by omega) := by
  have hL : (I.erase j).filter (· ≤ l) = I.filter (· ≤ l) := by
    rw [Finset.filter_erase]
    apply Finset.erase_eq_of_notMem
    simp only [Finset.mem_filter, not_and]
    intro _
    exact not_le_of_gt hlj
  have hjR : j ∈ I.filter (l ≤ ·) := Finset.mem_filter.mpr ⟨hj, hlj.le⟩
  have hdeg : 2 - (((I.filter (l ≤ ·)).erase j).card : ℤ) =
      2 - ((I.filter (l ≤ ·)).card : ℤ) + 1 := by
    have := Finset.card_erase_add_one hjR
    omega
  unfold dgModuleAugmentationHomotopyCut
  rw [hL, Finset.filter_erase, hdeg, dite_eq_left (by omega)]
  apply eq_of_heq
  refine gradedHom_compose_heq rfl rfl rfl rfl (by omega) rfl _ _ _ _ ?_ (HEq.rfl) _ _
  exact (dgModuleAugmentationHomotopyAt_heq R C E F (s.obj l) (s.obj b)
    (2 - ((I.filter (l ≤ ·)).card : ℤ) + 1) (2 - ((I.filter (l ≤ ·)).card : ℤ))
    (by omega) (s.homOrZero ((I.filter (l ≤ ·)).erase j) l b _)).symm
/-- 左側の一点削除後の実切断は、同じ右比較成分と左削除像の合成。 -/
lemma dgModuleAugmentationHomotopyCut_erase_left
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (j l : Fin (n + 1)) (hj : j ∈ I) (hjl : j < l)
    (hsum : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) = k) :
    dgModuleAugmentationHomotopyCut R C E F s (I.erase j) a b (k + 1) l =
    compose R (x := (s.obj a).replacement.val) (y := (s.obj l).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (dgModuleAugmentationHomotopyComponent R C E F (s.obj l) (s.obj b)
        (2 - ((I.filter (l ≤ ·)).card : ℤ))
        (s.homOrZero (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
        (s.homOrZero ((I.filter (· ≤ l)).erase j) a l
          (2 - ((I.filter (· ≤ l)).card : ℤ) + 1))) (by omega) := by
  have hR : (I.erase j).filter (l ≤ ·) = I.filter (l ≤ ·) := by
    rw [Finset.filter_erase]
    apply Finset.erase_eq_of_notMem
    simp only [Finset.mem_filter, not_and]
    intro _
    exact not_le_of_gt hjl
  have hjL : j ∈ I.filter (· ≤ l) := Finset.mem_filter.mpr ⟨hj, hjl.le⟩
  have hdeg : 2 - (((I.filter (· ≤ l)).erase j).card : ℤ) =
      2 - ((I.filter (· ≤ l)).card : ℤ) + 1 := by
    have := Finset.card_erase_add_one hjL
    omega
  unfold dgModuleAugmentationHomotopyCut
  rw [hR, Finset.filter_erase, hdeg, dite_eq_left (by omega)]
/-- 切断点の支持を制限しても、同じ削除・切断混合符号和は相殺する。 -/
lemma dgModuleAugmentation_sum_mixed_cancel_filter
    {α : Type*} [LinearOrder α] {M : Type*} [AddCommGroup M]
    (I K : Finset α) (hKI : K ⊆ I) (p : α → Prop) [DecidablePred p]
    (f : α → α → M) :
    (∑ j ∈ K, Index.sign I j • ∑ l ∈ (K.erase j).filter p,
      Index.sign (I.erase j) l • f j l) +
    (∑ l ∈ K.filter p, Index.sign I l • ∑ j ∈ K.filter (l < ·),
      Index.sign (I.filter (l ≤ ·)) j • f j l) +
    (∑ l ∈ K.filter p, Index.sign I l •
      ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
      ∑ j ∈ K.filter (· < l), Index.sign (I.filter (· ≤ l)) j • f j l)) = 0 := by
  classical
  simpa only [Finset.sum_filter, smul_ite, smul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero] using
    Index.sum_mixed_cancel I K hKI (fun j l ↦ if p l then f j l else 0)
/-- 右線形境界の同じ比較成分との合成は、右側の削除後の実切断和。 -/
lemma dgModuleAugmentationHomotopyCut_linear_right
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (l : Fin (n + 1)) (hal : a < l)
    (hsum : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) = k) :
    compose R (x := (s.obj a).replacement.val) (y := (s.obj l).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (dgModuleAugmentationHomotopyAt R C E F (s.obj l) (s.obj b)
        (2 - ((I.filter (l ≤ ·)).card : ℤ) + 1)
        (2 - ((I.filter (l ≤ ·)).card : ℤ)) (by omega)
        (s.linearBoundary (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
        (s.homOrZero (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ))))
      (by omega) =
    ∑ j ∈ (Index.interior I a b).filter (l < ·), Index.sign (I.filter (l ≤ ·)) j •
      dgModuleAugmentationHomotopyCut R C E F s (I.erase j) a b (k + 1) l := by
  rw [dgModuleAugmentationHomotopyAt_linearBoundary]
  simp only [compose_sum_left, compose_units_smul_left, Index.interior_right_cut I a b l hal]
  apply Finset.sum_congr rfl
  intro j hj
  have hm := Finset.mem_filter.mp hj
  have hjI := (Finset.mem_filter.mp hm.1).1
  rw [dgModuleAugmentationHomotopyCut_erase_right R C E F s I a b k j l hjI hm.2 hsum]
/-- 左線形境界の同じ入力像との合成は、左側の削除後の実切断和。 -/
lemma dgModuleAugmentationHomotopyCut_linear_left
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (l : Fin (n + 1)) (hlb : l < b)
    (hsum : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) = k) :
    compose R (x := (s.obj a).replacement.val) (y := (s.obj l).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (dgModuleAugmentationHomotopyComponent R C E F (s.obj l) (s.obj b)
        (2 - ((I.filter (l ≤ ·)).card : ℤ))
        (s.homOrZero (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
        (s.linearBoundary (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ))))
      (by omega) =
    ∑ j ∈ (Index.interior I a b).filter (· < l), Index.sign (I.filter (· ≤ l)) j •
      dgModuleAugmentationHomotopyCut R C E F s (I.erase j) a b (k + 1) l := by
  simp only [SimplexData.linearBoundary, Units.smul_def, map_sum, map_zsmul,
    compose_sum_right, Index.interior_left_cut I a b l hlb]
  apply Finset.sum_congr rfl
  intro j hj
  have hm := Finset.mem_filter.mp hj
  have hjI := (Finset.mem_filter.mp hm.1).1
  rw [dgModuleAugmentationHomotopyCut_erase_left R C E F s I a b k j l hjI hm.2 hsum]
  simpa only [Units.smul_def] using compose_units_smul_right (Index.sign (I.filter (· ≤ l)) j)
    (dgModuleAugmentationHomotopyComponent R C E F (s.obj l) (s.obj b) _
      (s.homOrZero (I.filter (l ≤ ·)) l b _))
    (((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
      (s.homOrZero ((I.filter (· ≤ l)).erase j) a l _)) (by omega)
end SerrePositivity.InfinityCategories
