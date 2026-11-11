module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOrderedFunctorDiagram
/-!
概要：順序相の実図式から全 HA 方程式と全面・退化に整合する dg nerve の単体を作る。
方針：同じ厳密変換と全斉次射の相間輸送、実関手の恒等・合成則を使う。
規約：関手圏の変換の等式は実単体で証明する。使われ方：kernel 比較の合成 coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
namespace DGOrderedFunctorDiagram
variable {R : Type u} [CommRing R] {C : Type v} {E : Type w}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] {κ : Type t} [Preorder κ]
  (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOrderedFunctorDiagram R C E κ)
/-- 対象と相の指定等式に沿って、同じ単位の輸送を異種等号で照合する。 -/
lemma transition_unit_of_heq {x y : C} (p q : κ) (hpq : p ≤ q)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y 0) (hxy : x = y) (hp : p = q)
    (hf : HEq f (_root_.SerrePositivity.DifferentialGraded.unitElement R y).val) :
    HEq (d.transition p q hpq f) (_root_.SerrePositivity.DifferentialGraded.unitElement R ((d.obj q).obj y)).val := by
  subst y q
  have he : f = (_root_.SerrePositivity.DifferentialGraded.unitElement R x).val := eq_of_heq hf
  subst f
  exact heq_of_eq (d.transition_unit p x)
/-- 同じ単調な相選択に沿って、元の単体の全係数を写す。 -/
def simplexData {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (β : Fin (n + 1) →o κ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R E n where
  obj a := (d.obj (β a)).obj (s.obj a)
  hom I a b k hI ha hb hk := d.transition (β a) (β b) (β.monotone (by
    rw [ha, hb]
    exact (I.isLeast_min' _).2 (I.max'_mem _))) (s.hom I a b k hI ha hb hk)

/-- 概要：順序相間の写像は内部点の符号付き寄与を保つ。
方針：符号・差・合成の保存を順に使う。
規約：HA Construction 1.3.1.6。使われ方：ホモトピー単体の右辺の各項。 -/
lemma simplexData_term {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (β : Fin (n + 1) →o κ)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    d.transition (β a) (β b) (β.monotone (haj.le.trans hjb.le))
      (s.term I a b k hI ha hb hk j hj haj hjb) =
        (d.simplexData s β).term I a b k hI ha hb hk j hj haj hjb := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.term, simplexData, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOrderedFunctorDiagram.transition_smul, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOrderedFunctorDiagram.transition_sub]
  rw [d.transition_compose (β a) (β j) (β b) (β.monotone haj.le) (β.monotone hjb.le)]

/-- 概要：順序相間の写像は単体方程式の右辺全体を保つ。
方針：有限和への分配と各内部点での寄与の保存を使う。
規約：HA Construction 1.3.1.6。使われ方：ホモトピー単体の方程式。 -/
lemma simplexData_rhs {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (β : Fin (n + 1) →o κ)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hab : a ≤ b) :
    d.transition (β a) (β b) (β.monotone hab) (s.rhs I a b k hI ha hb hk) =
      (d.simplexData s β).rhs I a b k hI ha hb hk := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  rw [d.transition_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hint : a < j.val ∧ j.val < b
  · simp only [dite_eq_left hint, simplexData_term]
  · simp only [dite_eq_right hint, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOrderedFunctorDiagram.transition_zero]

/-- 概要：単体と単調な順序相の選択からホモトピーの単体を作る。
方針：微分との可換性と右辺の保存により元の単体方程式を移す。
規約：HA Construction 1.3.1.6。使われ方：積と標準一単体からの写像の各次数。 -/
def simplex {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C n) (β : Fin (n + 1) →o κ) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R E n where
  toSimplexData := d.simplexData s.toSimplexData β
  equation I a b k hI ha hb hk := by
    have hab : a ≤ b := by
      rw [ha, hb]
      exact (I.isLeast_min' _).2 (I.max'_mem _)
    change _root_.SerrePositivity.DifferentialGraded.differential R (d.transition (β a) (β b) (β.monotone hab)
      (s.hom I a b k hI ha hb hk)) = _
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOrderedFunctorDiagram.transition_differential, s.equation, simplexData_rhs]
    exact hab

/-- 概要：順序相によるデータの構成は任意の単調写像による引き戻しと可換。
方針：単射・潰れた辺・高次の零の三分岐で、成分と単位の保存を使う。
規約：HA Construction 1.3.1.6。使われ方：積からの単体的写像の自然性。 -/
lemma simplexData_pullback {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n)
    (β : Fin (n + 1) →o κ) (α : Fin (m + 1) →o Fin (n + 1)) :
    d.simplexData (s.pullback α) (β.comp α) = (d.simplexData s β).pullback α := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext J a b k hJ ha hb hk
    change d.transition (β (α a)) (β (α b)) _ ((s.pullback α).hom J a b k hJ ha hb hk) =
      ((d.simplexData s β).pullback α).hom J a b k hJ ha hb hk
    by_cases hi : Set.InjOn α (J : Set (Fin (m + 1)))
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
      rfl
    · by_cases hc : J.card = 2
      · have hk0 : k = 0 := by omega
        subst hk0
        have hab : α a = α b := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.collapse_two hi hc
          (by rw [ha]; exact J.isLeast_min' _) (by rw [hb]; exact J.isGreatest_max' _)
        have hleft := d.transition_unit_of_heq (β (α a)) (β (α b)) (le_of_eq (congrArg β hab))
          ((s.pullback α).hom J a b 0 hJ ha hb hk) (congrArg s.obj hab) (congrArg β hab)
          (s.pullback_hom_of_collapsed_pair α J a b 0 hJ ha hb hk hi hc)
        have hright := (d.simplexData s β).pullback_hom_of_collapsed_pair
          α J a b 0 hJ ha hb hk hi hc
        exact eq_of_heq (hleft.trans hright.symm)
      · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc,
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc]
        exact d.transition_zero _ _ _

/-- 概要：ホモトピー単体の構成は単体の引き戻しと可換。
方針：データ部分の自然性と単体の外延性を使う。
規約：HA Construction 1.3.1.6。使われ方：単体的ホモトピーの自然性。 -/
lemma simplex_pullback {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C n)
    (β : Fin (n + 1) →o κ) (α : Fin (m + 1) →o Fin (n + 1)) :
    d.simplex (s.pullback α) (β.comp α) = (d.simplex s β).pullback α :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext (d.simplexData_pullback s.toSimplexData β α)

end DGOrderedFunctorDiagram
end SerrePositivity.InfinityCategories.Project.DerivedCategories
