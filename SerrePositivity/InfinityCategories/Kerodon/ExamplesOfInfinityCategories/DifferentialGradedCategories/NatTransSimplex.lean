module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans

/-! # 厳密 dg 自然変換によるホモトピー単体

概要：単調な二相の選択と dg nerve の単体から像の単体を構成する。
方針：相の間の斉次写像が微分・符号付き和・合成を保つことを使う。
規約：HA Construction 1.3.1.6。使われ方：厳密自然変換の単体的ホモトピー。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v w

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E] {F G : DGFunctor A D E}

namespace StrictNatTrans

variable (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)

/-- 概要：単体の頂点を単調な二相に従い F または G に写すデータ。
方針：全有限部分集合の成分に二相間の斉次写像を適用する。
規約：HA Construction 1.3.1.6。使われ方：ホモトピー単体のデータ。 -/
def simplexData {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (β : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A E n where
  obj a := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj F G (β a) (s.obj a)
  hom I a b k hI ha hb hk := η.transition (β a) (β b) (β.monotone (by
    rw [ha, hb]
    exact (I.isLeast_min' _).2 (I.max'_mem _))) (s.hom I a b k hI ha hb hk)

/-- 概要：二相間の写像は内部点の符号付き寄与を保つ。
方針：符号・差・合成の保存を順に使う。
規約：HA Construction 1.3.1.6。使われ方：ホモトピー単体の右辺の各項。 -/
lemma simplexData_term {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    η.transition (β a) (β b) (β.monotone (haj.le.trans hjb.le))
      (s.term I a b k hI ha hb hk j hj haj hjb) =
        (η.simplexData s β).term I a b k hI ha hb hk j hj haj hjb := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, simplexData, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.transition_smul, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.transition_sub]
  rw [η.transition_compose (β a) (β j) (β b) (β.monotone haj.le) (β.monotone hjb.le)]

/-- 概要：二相間の写像は単体方程式の右辺全体を保つ。
方針：有限和への分配と各内部点での寄与の保存を使う。
規約：HA Construction 1.3.1.6。使われ方：ホモトピー単体の方程式。 -/
lemma simplexData_rhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hab : a ≤ b) :
    η.transition (β a) (β b) (β.monotone hab) (s.rhs I a b k hI ha hb hk) =
      (η.simplexData s β).rhs I a b k hI ha hb hk := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  rw [η.transition_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hint : a < j.val ∧ j.val < b
  · simp only [dite_eq_left hint, simplexData_term]
  · simp only [dite_eq_right hint, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.transition_zero]

/-- 概要：単体と単調な二相の選択からホモトピーの単体を作る。
方針：微分との可換性と右辺の保存により元の単体方程式を移す。
規約：HA Construction 1.3.1.6。使われ方：積と標準一単体からの写像の各次数。 -/
def simplex {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n) (β : Fin (n + 1) →o Fin 2) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A E n where
  toSimplexData := η.simplexData s.toSimplexData β
  equation I a b k hI ha hb hk := by
    have hab : a ≤ b := by
      rw [ha, hb]
      exact (I.isLeast_min' _).2 (I.max'_mem _)
    change differential A (η.transition (β a) (β b) (β.monotone hab)
      (s.hom I a b k hI ha hb hk)) = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.transition_differential, s.equation, simplexData_rhs]
    exact hab

/-- 概要：二相によるデータの構成は任意の単調写像による引き戻しと可換。
方針：単射・潰れた辺・高次の零の三分岐で、成分と単位の保存を使う。
規約：HA Construction 1.3.1.6。使われ方：積からの単体的写像の自然性。 -/
lemma simplexData_pullback {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (β : Fin (n + 1) →o Fin 2) (α : Fin (m + 1) →o Fin (n + 1)) :
    η.simplexData (s.pullback α) (β.comp α) = (η.simplexData s β).pullback α := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext J a b k hJ ha hb hk
    change η.transition (β (α a)) (β (α b)) _ ((s.pullback α).hom J a b k hJ ha hb hk) =
      ((η.simplexData s β).pullback α).hom J a b k hJ ha hb hk
    by_cases hi : Set.InjOn α (J : Set (Fin (m + 1)))
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
      rfl
    · by_cases hc : J.card = 2
      · have hk0 : k = 0 := by omega
        subst hk0
        have hab : α a = α b := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.collapse_two hi hc
          (by rw [ha]; exact J.isLeast_min' _) (by rw [hb]; exact J.isGreatest_max' _)
        have hleft := η.transition_unit_of_heq (β (α a)) (β (α b)) (le_of_eq (congrArg β hab))
          ((s.pullback α).hom J a b 0 hJ ha hb hk) (congrArg s.obj hab) (congrArg β hab)
          (s.pullback_hom_of_collapsed_pair α J a b 0 hJ ha hb hk hi hc)
        have hright := (η.simplexData s β).pullback_hom_of_collapsed_pair
          α J a b 0 hJ ha hb hk hi hc
        exact eq_of_heq (hleft.trans hright.symm)
      · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc,
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc]
        exact η.transition_zero _ _ _

/-- 概要：ホモトピー単体の構成は単体の引き戻しと可換。
方針：データ部分の自然性と単体の外延性を使う。
規約：HA Construction 1.3.1.6。使われ方：単体的ホモトピーの自然性。 -/
lemma simplex_pullback {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (β : Fin (n + 1) →o Fin 2) (α : Fin (m + 1) →o Fin (n + 1)) :
    η.simplex (s.pullback α) (β.comp α) = (η.simplex s β).pullback α :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext (η.simplexData_pullback s.toSimplexData β α)

end StrictNatTrans

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
