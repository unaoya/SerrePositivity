module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PullbackEquation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DegeneracyIndex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Algebra

/-! # 退化の方程式の相殺

概要：隣接する同じ像の二点を含む成分について、他の内部点の寄与が零となることを示す。
方針：削除後にも重複点が残り、左右の切断の一方にも三点以上と重複点が残る。
規約：HA Construction 1.3.1.6。使われ方：退化の方程式を二項の相殺に帰着する。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：隣接する重複点以外の内部点の寄与は零。
方針：削除項と、重複点を含む側の切断成分を、非単射の高次成分として零にする。
規約：HA Construction 1.3.1.6。使われ方：一般の退化の右辺の有限和の整理。 -/
lemma pullback_term_of_collision_away {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (α : Fin (m + 2) →o Fin (n + 1)) (i : Fin (m + 1))
    (J : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hp : i.castSucc ∈ J) (hq : i.succ ∈ J)
    (he : α i.castSucc = α i.succ) (j : Fin (m + 2)) (hj : j ∈ J)
    (haj : a < j) (hjb : j < b) (hjp : j ≠ i.castSucc) (hjq : j ≠ i.succ) :
    (s.pullback α).term J a b k hJ ha hb hk j hj haj hjb = 0 := by
  have hamin : IsLeast (J : Set (Fin (m + 2))) a := by
    rw [ha]; exact J.isLeast_min' _
  have hbmax : IsGreatest (J : Set (Fin (m + 2))) b := by
    rw [hb]; exact J.isGreatest_max' _
  have hpE : i.castSucc ∈ J.erase j := Finset.mem_erase.mpr ⟨hjp.symm, hp⟩
  have hqE : i.succ ∈ J.erase j := Finset.mem_erase.mpr ⟨hjq.symm, hq⟩
  have hiE := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.not_injOn_of_equal hpE hqE (ne_of_lt Fin.castSucc_lt_succ) he
  have hE3 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.erase_three_of_internal i J hamin hbmax hp hq haj hjb hjp hjq
  have hE2 : (J.erase j).card ≠ 2 := by omega
  by_cases hji : j ≤ i.castSucc
  · have hjp' : j < i.castSucc := lt_of_le_of_ne hji hjp
    have hjR : j ∈ J.filter (j ≤ ·) := Finset.mem_filter.mpr ⟨hj, le_rfl⟩
    have hpR : i.castSucc ∈ J.filter (j ≤ ·) := Finset.mem_filter.mpr ⟨hp, hji⟩
    have hqR : i.succ ∈ J.filter (j ≤ ·) :=
      Finset.mem_filter.mpr ⟨hq, hji.trans Fin.castSucc_lt_succ.le⟩
    have hiR := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.not_injOn_of_equal hpR hqR (ne_of_lt Fin.castSucc_lt_succ) he
    have hR3 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.three_le_card hjR hpR hqR hjp' Fin.castSucc_lt_succ
    have hR2 : (J.filter (j ≤ ·)).card ≠ 2 := by omega
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback, dite_eq_right hiE, dite_eq_right hE2, dite_eq_right hiR,
      dite_eq_right hR2, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, sub_self, smul_zero]
  · have hqj : i.succ < j := by
      have hji' : ¬ j.val ≤ i.val := hji
      have hne : j.val ≠ i.val + 1 := fun h => hjq (Fin.ext h)
      change i.val + 1 < j.val
      omega
    have hpL : i.castSucc ∈ J.filter (· ≤ j) :=
      Finset.mem_filter.mpr ⟨hp, Fin.castSucc_lt_succ.le.trans hqj.le⟩
    have hqL : i.succ ∈ J.filter (· ≤ j) := Finset.mem_filter.mpr ⟨hq, hqj.le⟩
    have hjL : j ∈ J.filter (· ≤ j) := Finset.mem_filter.mpr ⟨hj, le_rfl⟩
    have hiL := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.not_injOn_of_equal hpL hqL (ne_of_lt Fin.castSucc_lt_succ) he
    have hL3 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.three_le_card hpL hqL hjL Fin.castSucc_lt_succ hqj
    have hL2 : (J.filter (· ≤ j)).card ≠ 2 := by omega
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback, dite_eq_right hiE, dite_eq_right hE2, dite_eq_right hiL,
      dite_eq_right hL2, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, sub_self, smul_zero]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (pullback_term_of_collision_away)


/-- 概要：基本退化の重複二点が両方内部にあるとき、その二点の項は相殺する。
方針：切断の合成項は零、削除の像は等しく、二つの符号は逆になる。
規約：HA Construction 1.3.1.6。使われ方：内部に重複を持つ退化単体の方程式。 -/
lemma predAbove_terms_cancel {m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D m) (i : Fin (m + 1))
    (J : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hp : i.castSucc ∈ J) (hq : i.succ ∈ J)
    (hap : a < i.castSucc) (hqb : i.succ < b) :
    (s.pullback i.predAboveOrderHom).term J a b k hJ ha hb hk i.castSucc hp hap
        (Fin.castSucc_lt_succ.trans hqb) +
      (s.pullback i.predAboveOrderHom).term J a b k hJ ha hb hk i.succ hq
        (hap.trans Fin.castSucc_lt_succ) hqb = 0 := by
  let α := i.predAboveOrderHom
  have he : α i.castSucc = α i.succ := by simp [α]
  have hamem : a ∈ J := by rw [ha]; exact J.min'_mem _
  have hbmem : b ∈ J := by rw [hb]; exact J.max'_mem _
  have hpR : i.castSucc ∈ J.filter (i.castSucc ≤ ·) := Finset.mem_filter.mpr ⟨hp, le_rfl⟩
  have hqR : i.succ ∈ J.filter (i.castSucc ≤ ·) :=
    Finset.mem_filter.mpr ⟨hq, Fin.castSucc_lt_succ.le⟩
  have hbR : b ∈ J.filter (i.castSucc ≤ ·) :=
    Finset.mem_filter.mpr ⟨hbmem, (Fin.castSucc_lt_succ.trans hqb).le⟩
  have hiR := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.not_injOn_of_equal hpR hqR (ne_of_lt Fin.castSucc_lt_succ) he
  have hR3 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.three_le_card hpR hqR hbR Fin.castSucc_lt_succ hqb
  have hR2 : (J.filter (i.castSucc ≤ ·)).card ≠ 2 := by omega
  have haL : a ∈ J.filter (· ≤ i.succ) :=
    Finset.mem_filter.mpr ⟨hamem, (hap.trans Fin.castSucc_lt_succ).le⟩
  have hpL : i.castSucc ∈ J.filter (· ≤ i.succ) :=
    Finset.mem_filter.mpr ⟨hp, Fin.castSucc_lt_succ.le⟩
  have hqL : i.succ ∈ J.filter (· ≤ i.succ) := Finset.mem_filter.mpr ⟨hq, le_rfl⟩
  have hiL := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.not_injOn_of_equal hpL hqL (ne_of_lt Fin.castSucc_lt_succ) he
  have hL3 := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.three_le_card haL hpL hqL hap Fin.castSucc_lt_succ
  have hL2 : (J.filter (· ≤ i.succ)).card ≠ 2 := by omega
  have hiEP : Set.InjOn α ((J.erase i.castSucc) : Set (Fin (m + 2))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.predAbove_injOn_of_not_left i (by simp)
  have hiEQ : Set.InjOn α ((J.erase i.succ) : Set (Fin (m + 2))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.predAbove_injOn_of_not_right i (by simp)
  dsimp only [α] at hiR hiL hiEP hiEQ
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback, dite_eq_right hiR,
    dite_eq_right hR2, dite_eq_right hiL, dite_eq_right hL2, dite_eq_left hiEP,
    dite_eq_left hiEQ, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, sub_zero]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.predAbove_sign_card i J hq]
  have hImage : (J.erase i.castSucc).image i.predAboveOrderHom =
      (J.erase i.succ).image i.predAboveOrderHom := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.predAbove_image_erase i J hp hq
  simp [Nat.cast_add, Int.negOnePow_add, Units.smul_def, hImage]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (predAbove_terms_cancel)


/-- 概要：重複する二点が両方内部にある場合、基本退化の方程式の右辺は零。
方針：有限和を重複二点の項だけに制限し、その二項の相殺を使う。
規約：HA Construction 1.3.1.6。使われ方：内部で退化する単体の方程式の保存。 -/
lemma predAbove_rhs_of_interior {m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D m) (i : Fin (m + 1))
    (J : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hp : i.castSucc ∈ J) (hq : i.succ ∈ J)
    (hap : a < i.castSucc) (hqb : i.succ < b) :
    (s.pullback i.predAboveOrderHom).rhs J a b k hJ ha hb hk = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  have hpq : (⟨i.castSucc, hp⟩ : J) ≠ ⟨i.succ, hq⟩ := by
    intro h
    exact (ne_of_lt Fin.castSucc_lt_succ) (congrArg Subtype.val h)
  rw [Finset.sum_eq_add_of_mem (⟨i.castSucc, hp⟩ : J) (⟨i.succ, hq⟩ : J)
    (Finset.mem_univ _) (Finset.mem_univ _) hpq]
  · simp only [dite_eq_left (And.intro hap (Fin.castSucc_lt_succ.trans hqb)),
      dite_eq_left (And.intro (hap.trans Fin.castSucc_lt_succ) hqb)]
    exact s.predAbove_terms_cancel i J a b k hJ ha hb hk hp hq hap hqb
  · intro j _ hj
    by_cases h : a < j.val ∧ j.val < b
    · simp only [dite_eq_left h]
      exact s.pullback_term_of_collision_away i.predAboveOrderHom i J a b k hJ ha hb hk
        hp hq (by simp) j.val j.property h.1 h.2
        (fun he => hj.1 (Subtype.ext he)) (fun he => hj.2 (Subtype.ext he))
    · exact dite_eq_right h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (predAbove_rhs_of_interior)


/-- 概要：左重複点が始点のとき、右重複点の項は零。
方針：左切断が潰れた辺の単位になり、右切断と削除の像が一致するので左単位則を使う。
規約：HA Construction 1.3.1.6。使われ方：始点に接する退化の方程式。 -/
lemma predAbove_term_of_min {m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D m) (i : Fin (m + 1))
    (J : Finset (Fin (m + 2))) (b : Fin (m + 2)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : i.castSucc = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ))
    (hq : i.succ ∈ J) (hqb : i.succ < b) :
    (s.pullback i.predAboveOrderHom).term J i.castSucc b k hJ ha hb hk
      i.succ hq Fin.castSucc_lt_succ hqb = 0 := by
  let α := i.predAboveOrderHom
  have hamin : IsLeast (J : Set (Fin (m + 2))) i.castSucc := by
    rw [ha]; exact J.isLeast_min' _
  have hp := hamin.1
  have hLeft := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.predAbove_left_of_min i J hamin hq
  have hRight := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.predAbove_right_of_min i J hamin
  have hL2 : (J.filter (· ≤ i.succ)).card = 2 := by
    rw [hLeft]
    simp [ne_of_lt Fin.castSucc_lt_succ]
  have hiL : ¬ Set.InjOn α ((J.filter (· ≤ i.succ)) : Set (Fin (m + 2))) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.not_injOn_of_equal (J := J.filter (· ≤ i.succ)) (f := α)
      (p := i.castSucc) (q := i.succ)
      (Finset.mem_filter.mpr ⟨hp, Fin.castSucc_lt_succ.le⟩)
      (Finset.mem_filter.mpr ⟨hq, le_rfl⟩) (ne_of_lt Fin.castSucc_lt_succ)
    simp [α]
  have hiR : Set.InjOn α ((J.filter (i.succ ≤ ·)) : Set (Fin (m + 2))) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.predAbove_injOn_of_not_left
    simp only [Finset.mem_filter, not_and]
    intro _
    exact not_le_of_gt Fin.castSucc_lt_succ
  have hiEQ : Set.InjOn α ((J.erase i.succ) : Set (Fin (m + 2))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.predAbove_injOn_of_not_right i (by simp)
  have hImage : (J.filter (i.succ ≤ ·)).image i.predAboveOrderHom =
      (J.erase i.succ).image i.predAboveOrderHom := by
    rw [hRight]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.predAbove_image_erase i J hp hq
  have hDegree : 2 - ((J.filter (i.succ ≤ ·)).card : ℤ) = k + 1 := by
    rw [hRight]
    have hc := Finset.card_erase_add_one hp
    omega
  have he : i.predAboveOrderHom i.castSucc = i.predAboveOrderHom i.succ := by simp
  have hUnit := s.pullback_hom_of_collapsed_pair α (J.filter (· ≤ i.succ))
    i.castSucc i.succ (2 - ((J.filter (· ≤ i.succ)).card : ℤ))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_two hp hq Fin.castSucc_lt_succ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_min hamin Fin.castSucc_lt_succ.le _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.left_max hq _) rfl hiL hL2
  dsimp only [α] at hiL hiR hiEQ hUnit
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback, dite_eq_right hiL, dite_eq_left hL2,
    dite_eq_left hiR, dite_eq_left hiEQ]
  rw [smul_eq_zero_iff_eq, sub_eq_zero]
  symm
  apply eq_of_heq
  refine HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_unit_of_heq _ _ _ (congrArg s.obj he) ?_ ?_) ?_
  · simp [hL2]
  · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback, dite_eq_right hiL, dite_eq_left hL2] using hUnit
  · congr! 1; simp_all

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (predAbove_term_of_min)


/-- 概要：右重複点が終点のとき、左重複点の項は零。
方針：右切断が潰れた辺の単位になり、左切断と削除の像が一致するので右単位則を使う。
規約：HA Construction 1.3.1.6。使われ方：終点に接する退化の方程式。 -/
lemma predAbove_term_of_max {m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D m) (i : Fin (m + 1))
    (J : Finset (Fin (m + 2))) (a : Fin (m + 2)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : i.succ = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ))
    (hp : i.castSucc ∈ J) (hap : a < i.castSucc) :
    (s.pullback i.predAboveOrderHom).term J a i.succ k hJ ha hb hk
      i.castSucc hp hap Fin.castSucc_lt_succ = 0 := by
  let α := i.predAboveOrderHom
  have hbmax : IsGreatest (J : Set (Fin (m + 2))) i.succ := by
    rw [hb]; exact J.isGreatest_max' _
  have hq := hbmax.1
  have hLeft := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.predAbove_left_of_max i J hbmax
  have hRight := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.predAbove_right_of_max i J hp hbmax
  have hR2 : (J.filter (i.castSucc ≤ ·)).card = 2 := by
    rw [hRight]
    simp [ne_of_lt Fin.castSucc_lt_succ]
  have hiR : ¬ Set.InjOn α ((J.filter (i.castSucc ≤ ·)) : Set (Fin (m + 2))) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.not_injOn_of_equal (J := J.filter (i.castSucc ≤ ·)) (f := α)
      (p := i.castSucc) (q := i.succ)
      (Finset.mem_filter.mpr ⟨hp, le_rfl⟩)
      (Finset.mem_filter.mpr ⟨hq, Fin.castSucc_lt_succ.le⟩) (ne_of_lt Fin.castSucc_lt_succ)
    simp [α]
  have hiL : Set.InjOn α ((J.filter (· ≤ i.castSucc)) : Set (Fin (m + 2))) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.predAbove_injOn_of_not_right
    simp only [Finset.mem_filter, not_and]
    intro _
    exact not_le_of_gt Fin.castSucc_lt_succ
  have hiEP : Set.InjOn α ((J.erase i.castSucc) : Set (Fin (m + 2))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.predAbove_injOn_of_not_left i (by simp)
  have hImage : (J.filter (· ≤ i.castSucc)).image i.predAboveOrderHom =
      (J.erase i.castSucc).image i.predAboveOrderHom := by
    rw [hLeft]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.predAbove_image_erase i J hp hq).symm
  have hDegree : 2 - ((J.filter (· ≤ i.castSucc)).card : ℤ) = k + 1 := by
    rw [hLeft]
    have hc := Finset.card_erase_add_one hq
    omega
  have he : i.predAboveOrderHom i.castSucc = i.predAboveOrderHom i.succ := by simp
  have hUnit := s.pullback_hom_of_collapsed_pair α (J.filter (i.castSucc ≤ ·))
    i.castSucc i.succ (2 - ((J.filter (i.castSucc ≤ ·)).card : ℤ))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_two hp hq Fin.castSucc_lt_succ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min hp _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_max hbmax Fin.castSucc_lt_succ.le _) rfl hiR hR2
  dsimp only [α] at hiL hiR hiEP hUnit
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback, dite_eq_right hiR, dite_eq_left hR2,
    dite_eq_left hiL, dite_eq_left hiEP]
  rw [smul_eq_zero_iff_eq, sub_eq_zero]
  symm
  apply eq_of_heq
  refine HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.unit_compose_of_heq _ _ _ (congrArg s.obj he) ?_ ?_) ?_
  · simp [hR2]
  · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback, dite_eq_right hiR, dite_eq_left hR2] using hUnit
  · congr! 1

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (predAbove_term_of_max)


/-- 概要：基本退化の重複二点を含む集合では、方程式の右辺は零。
方針：内部の重複は二項の相殺、始点・終点での重複は単位則に帰着する。
規約：HA Construction 1.3.1.6。使われ方：基本退化写像の方程式の保存。 -/
lemma predAbove_rhs_of_collision {m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D m) (i : Fin (m + 1))
    (J : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hp : i.castSucc ∈ J) (hq : i.succ ∈ J) :
    (s.pullback i.predAboveOrderHom).rhs J a b k hJ ha hb hk = 0 := by
  have hamin : IsLeast (J : Set (Fin (m + 2))) a := by
    rw [ha]; exact J.isLeast_min' _
  have hbmax : IsGreatest (J : Set (Fin (m + 2))) b := by
    rw [hb]; exact J.isGreatest_max' _
  by_cases hap : a = i.castSucc
  · subst hap
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
    apply Finset.sum_eq_zero
    intro j _
    by_cases h : i.castSucc < j.val ∧ j.val < b
    · simp only [dite_eq_left h]
      by_cases hjq : j.val = i.succ
      · have hj' : j = ⟨i.succ, hq⟩ := Subtype.ext hjq
        subst hj'
        exact s.predAbove_term_of_min i J b k hJ ha hb hk hq h.2
      · exact s.pullback_term_of_collision_away i.predAboveOrderHom i J i.castSucc b k
          hJ ha hb hk hp hq (by simp) j.val j.property h.1 h.2 (ne_of_gt h.1) hjq
    · exact dite_eq_right h
  · have hap' : a < i.castSucc := lt_of_le_of_ne (hamin.2 hp) hap
    by_cases hbq : b = i.succ
    · subst hbq
      unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
      apply Finset.sum_eq_zero
      intro j _
      by_cases h : a < j.val ∧ j.val < i.succ
      · simp only [dite_eq_left h]
        by_cases hjp : j.val = i.castSucc
        · have hj' : j = ⟨i.castSucc, hp⟩ := Subtype.ext hjp
          subst hj'
          exact s.predAbove_term_of_max i J a k hJ ha hb hk hp h.1
        · exact s.pullback_term_of_collision_away i.predAboveOrderHom i J a i.succ k
            hJ ha hb hk hp hq (by simp) j.val j.property h.1 h.2 hjp (ne_of_lt h.2)
      · exact dite_eq_right h
    · exact s.predAbove_rhs_of_interior i J a b k hJ ha hb hk hp hq hap'
        (lt_of_le_of_ne (hbmax.2 hq) (Ne.symm hbq))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (predAbove_rhs_of_collision)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：基本退化写像による引き戻しは全ての単体の方程式を保つ。
方針：単射の部分集合、二点集合、重複二点を含む高次集合に場合分けする。
規約：HA Construction 1.3.1.6。使われ方：一般の単調写像による引き戻しの帰納法。 -/
lemma predAbove_equation {m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D m) (i : Fin (m + 1))
    (J : Finset (Fin (m + 2))) (a b : Fin (m + 2)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) :
    differential A ((s.toSimplexData.pullback i.predAboveOrderHom).hom J a b k hJ ha hb hk) =
      (s.toSimplexData.pullback i.predAboveOrderHom).rhs J a b k hJ ha hb hk := by
  by_cases hi : Set.InjOn i.predAboveOrderHom (J : Set (Fin (m + 2)))
  · exact s.pullback_equation_of_inj i.predAboveOrderHom J a b k hJ ha hb hk hi
  by_cases hc : J.card = 2
  · exact s.pullback_equation_of_card_two i.predAboveOrderHom J a b k hJ ha hb hk hc
  have hi' : ¬ Set.InjOn i.predAbove (J : Set (Fin (m + 2))) := hi
  have hpq : i.castSucc ∈ J ∧ i.succ ∈ J :=
    not_not.mp ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.predAbove_injOn_iff i J).not.mp hi')
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc,
    SimplexData.predAbove_rhs_of_collision _ _ _ _ _ _ _ _ _ _ hpq.1 hpq.2]
  simp [differential]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (predAbove_equation)


/-- 概要：基本退化写像は m 単体から m+1 単体を作る。
方針：引き戻したデータに基本退化の方程式の保存を添える。
規約：HA Construction 1.3.1.6。使われ方：一般の引き戻しの構成と退化の計算。 -/
def degeneracy {m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D m) (i : Fin (m + 1)) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D (m + 1) where
  toSimplexData := s.toSimplexData.pullback i.predAboveOrderHom
  equation J a b k hJ ha hb hk := s.predAbove_equation i J a b k hJ ha hb hk

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (degeneracy)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
