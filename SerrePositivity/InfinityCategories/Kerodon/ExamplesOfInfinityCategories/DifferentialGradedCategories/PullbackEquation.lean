module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex

/-! # 単体の方程式と引き戻し

概要：単射の添字変更による方程式の各項の移送を証明する。
方針：削除・左右切断の像と濃度の補題を使う。
規約：HA Construction 1.3.1.6。使われ方：単体的構造の方程式の保存。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：二点集合での方程式の右辺は零。
方針：集合の元は両端だけなので内部点の項がない。
規約：HA Example 1.3.1.8。使われ方：潰れる辺の方程式の保存。 -/
lemma rhs_of_card_two {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hc : J.card = 2) : s.rhs J a b k hJ ha hb hk = 0 := by
  have hpair : J = {a, b} := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.eq_pair hc
    (by rw [ha]; exact J.isLeast_min' _) (by rw [hb]; exact J.isGreatest_max' _)
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  apply Finset.sum_eq_zero
  intro j _
  have hj : j.val = a ∨ j.val = b := by simpa [hpair] using j.property
  rcases hj with h | h
  · simp [h]
  · simp [h]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (rhs_of_card_two)


/-- 概要：部分集合上で単射の添字変更は微分方程式の内部点の各項を保つ。
方針：像と削除・切断が可換であることと、符号の指数の保存を使う。
規約：HA Construction 1.3.1.6。使われ方：右辺の有限和の再添字付け。 -/
lemma pullback_term_of_inj {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (α : Fin (m + 1) →o Fin (n + 1)) (J : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hi : Set.InjOn α (J : Set (Fin (m + 1))))
    (j : Fin (m + 1)) (hj : j ∈ J) (haj : a < j) (hjb : j < b) :
    (s.pullback α).term J a b k hJ ha hb hk j hj haj hjb =
      s.term (J.image α) (α a) (α b) k (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hi hJ)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone (by rw [ha]; exact J.isLeast_min' _) _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone (by rw [hb]; exact J.isGreatest_max' _) _)
        (by rw [Finset.card_image_of_injOn hi]; exact hk)
        (α j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_lt_iff α.monotone hi (ha ▸ J.min'_mem _) hj).mpr haj)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_lt_iff α.monotone hi hj (hb ▸ J.max'_mem _)).mpr hjb) := by
  have hiE : Set.InjOn α ((J.erase j) : Set (Fin (m + 1))) :=
    hi.mono (by intro x hx; exact (Finset.mem_erase.mp hx).2)
  have hiL : Set.InjOn α ((J.filter (· ≤ j)) : Set (Fin (m + 1))) :=
    hi.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)
  have hiR : Set.InjOn α ((J.filter (j ≤ ·)) : Set (Fin (m + 1))) :=
    hi.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_erase hi hj
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_left α.monotone hi hj
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_right α.monotone hi hj
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback, dite_eq_left hiE, dite_eq_left hiL, dite_eq_left hiR,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_sign_card α.monotone hi hj]
  congr 2 <;> simp only [← he, ← hl, ← hr]
  congr! 2 <;> simp_all [← hl, ← hr, Finset.card_image_of_injOn hiL,
    Finset.card_image_of_injOn hiR]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (pullback_term_of_inj)


/-- 概要：部分集合上で単射の添字変更は微分方程式の右辺を保つ。
方針：所属証明付きの有限集合とその像の間の全単射で有限和を移送する。
規約：HA Construction 1.3.1.6。使われ方：単射の場合の方程式の保存。 -/
lemma pullback_rhs_of_inj {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (α : Fin (m + 1) →o Fin (n + 1)) (J : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hi : Set.InjOn α (J : Set (Fin (m + 1)))) :
    (s.pullback α).rhs J a b k hJ ha hb hk =
      s.rhs (J.image α) (α a) (α b) k (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hi hJ)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone (by rw [ha]; exact J.isLeast_min' _) _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone (by rw [hb]; exact J.isGreatest_max' _) _)
        (by rw [Finset.card_image_of_injOn hi]; exact hk) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  let f : J → J.image α := fun j => ⟨α j.val, Finset.mem_image.mpr ⟨j.val, j.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact hi x.property y.property (congrArg Subtype.val h)
    · intro y
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp y.property
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  refine Fintype.sum_bijective f hf _ _ ?_
  intro j
  have hamem : a ∈ J := by rw [ha]; exact J.min'_mem _
  have hbmem : b ∈ J := by rw [hb]; exact J.max'_mem _
  have hcond : (a < j.val ∧ j.val < b) ↔ (α a < α j.val ∧ α j.val < α b) :=
    and_congr (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_lt_iff α.monotone hi hamem j.property).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_lt_iff α.monotone hi j.property hbmem).symm
  dsimp only [f]
  by_cases h : a < j.val ∧ j.val < b
  · simp only [dite_eq_left h, dite_eq_left (hcond.mp h)]
    exact s.pullback_term_of_inj α J a b k hJ ha hb hk hi j.val j.property h.1 h.2
  · have h' : ¬ (α a < α j.val ∧ α j.val < α b) := fun hh => h (hcond.mpr hh)
    simp only [dite_eq_right h, dite_eq_right h']

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (pullback_rhs_of_inj)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：部分集合上で単射の引き戻しは、その部分集合の単体の方程式を満たす。
方針：微分する成分と方程式の右辺の両方を像に移送し、元の単体の方程式を使う。
規約：HA Construction 1.3.1.6。使われ方：一般の引き戻しの単射分岐。 -/
lemma pullback_equation_of_inj {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (α : Fin (m + 1) →o Fin (n + 1)) (J : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hi : Set.InjOn α (J : Set (Fin (m + 1)))) :
    differential A ((s.toSimplexData.pullback α).hom J a b k hJ ha hb hk) =
      (s.toSimplexData.pullback α).rhs J a b k hJ ha hb hk := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi,
    SimplexData.pullback_rhs_of_inj _ _ _ _ _ _ _ _ _ _ hi]
  exact s.equation _ _ _ _ _ _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (pullback_equation_of_inj)


/-- 概要：単射な単調写像に沿って単体を引き戻せる。
方針：全ての部分集合上の単射性から方程式の保存を得る。
規約：HA Construction 1.3.1.6。使われ方：面写像の構成。
一般の非単射写像による退化写像の存在は、この宣言の主張には含まない。 -/
def pullbackOfInjective {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (α : Fin (m + 1) →o Fin (n + 1)) (hi : Function.Injective α) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D m where
  toSimplexData := s.toSimplexData.pullback α
  equation J a b k hJ ha hb hk :=
    s.pullback_equation_of_inj α J a b k hJ ha hb hk hi.injOn

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (pullbackOfInjective)


/-- 概要：任意の単調写像による引き戻しは二点集合の方程式を満たす。
方針：単射なら像の辺の閉性を使い、潰れた辺なら dg 単位の閉性を使う。
規約：HA Construction 1.3.1.6。使われ方：非単射の場合の次数零の検証。 -/
lemma pullback_equation_of_card_two {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (α : Fin (m + 1) →o Fin (n + 1)) (J : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hc : J.card = 2) :
    differential A ((s.toSimplexData.pullback α).hom J a b k hJ ha hb hk) =
      (s.toSimplexData.pullback α).rhs J a b k hJ ha hb hk := by
  by_cases hi : Set.InjOn α (J : Set (Fin (m + 1)))
  · exact s.pullback_equation_of_inj α J a b k hJ ha hb hk hi
  rw [SimplexData.rhs_of_card_two _ _ _ _ _ _ _ _ _ hc]
  have hk' : k = 0 := by omega
  subst hk'
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback, dite_eq_right hi, dite_eq_left hc]
  have hab : α a = α b := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.collapse_two hi hc
    (by rw [ha]; exact J.isLeast_min' _) (by rw [hb]; exact J.isGreatest_max' _)
  have hcast : ∀ (x y : D) (_ : x = y)
      (he : (GradedHom A y y 0 : Type u) = (GradedHom A x y 0 : Type u)),
      differential A (cast he (unitElement A y).val) = 0 := by
    intro x y h he
    cases h
    exact differential_unit A x
  exact hcast _ _ (congrArg s.obj hab) _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex export _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories (pullback_equation_of_card_two)


end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
