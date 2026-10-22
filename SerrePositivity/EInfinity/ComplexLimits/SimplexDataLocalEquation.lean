module
public import SerrePositivity.InfinityCategories.DGNerve.PinchedRhs
public import SerrePositivity.InfinityCategories.DGNerve.FixedEquation

/-!
概要：部分集合の全 cochain が一致するデータへ、元の実単体の全方程式を移す。
方針：全成分・全切断・微分の比較を端点の等式輸送と両立させる。
規約：元の実単体と同じ対象・次数を保持する。使われ方：大域評価三角形の全 HA。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories DGNerve
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

abbrev SimplexDataHomAgreementOn {n : ℕ} (s t : SimplexData A D n)
    (I : Finset (Fin (n + 1))) : Prop :=
  ∀ (J : Finset (Fin (n + 1))), J ⊆ I →
    ∀ a b k hJ ha hb hk, HEq (s.hom J a b k hJ ha hb hk) (t.hom J a b k hJ ha hb hk)

lemma simplexData_term_heq_of_agreementOn {n : ℕ} (s t : SimplexData A D n)
    (I : Finset (Fin (n + 1)))
    (hx : ∀ i ∈ I, s.obj i = t.obj i) (h : SimplexDataHomAgreementOn s t I)
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I)
    (haj : a < j) (hjb : j < b) :
    HEq (s.term I a b k hI ha hb hk j hj haj hjb)
      (t.term I a b k hI ha hb hk j hj haj hjb) := by
  have haI : a ∈ I := by rw [ha]; exact I.min'_mem _
  have hbI : b ∈ I := by rw [hb]; exact I.max'_mem _
  dsimp only [SimplexData.term]
  apply smul_sub_heq_of_obj_eq (hx a haI) (hx b hbI)
  · exact h _ (Finset.erase_subset _ _) _ _ _ _ _ _ _
  · exact gradedHom_compose_heq (hx a haI) (hx j hj) (hx b hbI) rfl rfl rfl
      _ _ _ _ (h _ (Finset.filter_subset _ _) _ _ _ _ _ _ _)
      (h _ (Finset.filter_subset _ _) _ _ _ _ _ _ _) _ _

lemma simplexData_rhs_heq_of_agreementOn {n : ℕ} (s t : SimplexData A D n)
    (I : Finset (Fin (n + 1)))
    (hx : ∀ i ∈ I, s.obj i = t.obj i) (h : SimplexDataHomAgreementOn s t I)
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    HEq (s.rhs I a b k hI ha hb hk) (t.rhs I a b k hI ha hb hk) := by
  have haI : a ∈ I := by rw [ha]; exact I.min'_mem _
  have hbI : b ∈ I := by rw [hb]; exact I.max'_mem _
  unfold SimplexData.rhs
  apply sum_heq_of_obj_eq (hx a haI) (hx b hbI)
  intro j
  by_cases hint : a < j.val ∧ j.val < b
  · simp only [dite_eq_left hint]
    exact simplexData_term_heq_of_agreementOn s t I hx h a b k hI ha hb hk
      j.val j.property hint.1 hint.2
  · simp only [dite_eq_right hint]
    exact gradedHom_zero_heq (hx a haI) (hx b hbI) rfl

lemma simplexData_equation_of_agreementOn {n : ℕ} (s : SimplexData A D n) (t : Simplex A D n)
    (I : Finset (Fin (n + 1)))
    (hx : ∀ i ∈ I, s.obj i = t.obj i)
    (h : SimplexDataHomAgreementOn s t.toSimplexData I) : s.Equation I := by
  intro a b k hI ha hb hk
  have haI : a ∈ I := by rw [ha]; exact I.min'_mem _
  have hbI : b ∈ I := by rw [hb]; exact I.max'_mem _
  have hd := gradedHom_differential_heq (hx a haI) (hx b hbI) rfl _ _
    (h I (Finset.Subset.refl I) a b k hI ha hb hk)
  have hr := simplexData_rhs_heq_of_agreementOn s t.toSimplexData I hx h a b k hI ha hb hk
  exact eq_of_heq (hd.trans ((heq_of_eq (t.equation I a b k hI ha hb hk)).trans hr.symm))
end SerrePositivity.EInfinity.ComplexLimits
