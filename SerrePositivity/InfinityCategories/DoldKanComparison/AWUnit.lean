module

public import SerrePositivity.InfinityCategories.DoldKanComparison.AWUnitIndex

/-!
# AW 成分族の単位則

概要：dg 単位の定数単体は AW 成分族の演算の両側単位である。
方針：単位成分が残る切断点は最小点または最大点だけであることを使う。
規約：標準方程式を満たすという追加仮定は前の射の成分族に要求しない。
使われ方：HA 1.3.1.13、Kerodon 2.5.8 の豊穣単位則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DoldKanComparison

open CategoryTheory DifferentialGraded DGNerve.PinchedHom

variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y : D}

/-- 概要：同じ集合を表す二つの成分は次数も含めて異種等号で一致する。
方針：集合の等式から次数の等式を導き、両等式を消去する。
規約：次数の証明を保持した成分族に対して述べる。
使われ方：Kerodon 2.5.8 の切断集合の置換と斉次合成の単位則。 -/
lemma component_heq_of_eq {n : ℕ} (f : LinearData R x y n)
    (I J : Finset (Fin (n + 1))) (hIJ : I = J) (p q : ℤ)
    (hI : I.Nonempty) (hJ : J.Nonempty) (hp : p = 1 - (I.card : ℤ))
    (hq : q = 1 - (J.card : ℤ)) : HEq (f.component I p hI hp) (f.component J q hJ hq) := by
  subst J
  have hpq : p = q := hp.trans hq.symm
  subst hpq
  rfl

/-- 概要：定数単体の一点成分は次数を含めて指定した閉零射に等しい。
方針：濃度一の集合を一点集合に書き換えて評価する。
規約：指定された成分の次数はその濃度から零に決まる。
使われ方：Kerodon 2.5.8 の単位の切断成分の評価。 -/
lemma standardConstant_component_heq (z : zeroCycles (homObject R D x y)) {n : ℕ}
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hc : J.card = 1) : HEq ((standardConstant z n).val.component J k hJ hk) z.val := by
  obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hc
  have hkk : k = 0 := by simpa using hk
  subst hkk
  exact heq_of_eq (standardConstant_singleton z j)

/-- 概要：後の射が単位である AW の最小切断点の項は元の成分である。
方針：接頭部分は一点、接尾部分は全体となり dg 単位則を使える。
規約：通常順 compose では後の射の単位が左単位である。
使われ方：HA 1.3.1.13 の AW 左単位則の唯一の非零項。 -/
lemma awTerm_unit_left_min {n : ℕ} (f : LinearData R x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    awTerm (standardConstant (unitElement R y) n).val f J
      ⟨J.min' hJ, J.min'_mem hJ⟩ k hk = f.component J k hJ hk := by
  have hg := standardConstant_component_heq (unitElement R y) (J.filter (· ≤ J.min' hJ))
    _ (AWIndex.left_nonempty (J.min'_mem hJ)) rfl
    (by rw [AWIndex.left_at_min hJ]; simp)
  have he := DGNerve.unit_compose_of_heq (k := k)
    ((standardConstant (unitElement R y) n).val.component (J.filter (· ≤ J.min' hJ)) _
      (AWIndex.left_nonempty (J.min'_mem hJ)) rfl)
    (f.component (J.filter (J.min' hJ ≤ ·)) _
      (AWIndex.right_nonempty (J.min'_mem hJ)) rfl)
    (by rw [AWIndex.degree_add (J.min'_mem hJ)]; exact hk.symm)
    rfl (by rw [AWIndex.left_at_min hJ]; simp) hg
  exact eq_of_heq (he.trans (component_heq_of_eq f _ _ (AWIndex.right_at_min hJ) _ _ _ hJ rfl hk))

/-- 概要：前の射が単位である AW の最大切断点の項は元の成分である。
方針：接頭部分は全体、接尾部分は一点となり dg 単位則を使える。
規約：通常順 compose では前の射の単位が右単位である。
使われ方：HA 1.3.1.13 の AW 右単位則の唯一の非零項。 -/
lemma awTerm_unit_right_max {n : ℕ} (g : LinearData R x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    awTerm g (standardConstant (unitElement R x) n).val J
      ⟨J.max' hJ, J.max'_mem hJ⟩ k hk = g.component J k hJ hk := by
  have hf := standardConstant_component_heq (unitElement R x) (J.filter (J.max' hJ ≤ ·))
    _ (AWIndex.right_nonempty (J.max'_mem hJ)) rfl
    (by rw [AWIndex.right_at_max hJ]; simp)
  have he := DGNerve.compose_unit_of_heq (k := k)
    (g.component (J.filter (· ≤ J.max' hJ)) _
      (AWIndex.left_nonempty (J.max'_mem hJ)) rfl)
    ((standardConstant (unitElement R x) n).val.component (J.filter (J.max' hJ ≤ ·)) _
      (AWIndex.right_nonempty (J.max'_mem hJ)) rfl)
    (by rw [AWIndex.degree_add (J.max'_mem hJ)]; exact hk.symm)
    rfl (by rw [AWIndex.right_at_max hJ]; simp) hf
  exact eq_of_heq (he.trans (component_heq_of_eq g _ _ (AWIndex.left_at_max hJ) _ _ _ hJ rfl hk))

/-- 概要：dg 単位の定数単体は AW 成分族の演算の左単位である。
方針：最小切断点の項を取り出し、他は単位の高次成分が零として消す。
規約：任意の成分族に成立し、方程式の保存を仮定しない。
使われ方：HA 1.3.1.13 の豊穣合成の左単位則。 -/
lemma awData_unit_left {n : ℕ} (f : LinearData R x y n) :
    awData (standardConstant (unitElement R y) n).val f = f := by
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (awData _ f).component J k hJ hk = f.component J k hJ hk
  rw [awData_component, Finset.sum_eq_single (⟨J.min' hJ, J.min'_mem hJ⟩ : J)]
  · exact awTerm_unit_left_min f J k hJ hk
  · intro j _ hj
    have hne : j.val ≠ J.min' hJ := fun he ↦ hj (Subtype.ext he)
    unfold awTerm
    rw [standardConstant_component_zero _ _ _ _ _ (AWIndex.left_two_of_ne_min hJ j.property hne)]
    exact DGNerve.zero_compose _ _
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- 概要：dg 単位の定数単体は AW 成分族の演算の右単位である。
方針：最大切断点の項を取り出し、他は単位の高次成分が零として消す。
規約：任意の成分族に成立し、方程式の保存を仮定しない。
使われ方：HA 1.3.1.13 の豊穣合成の右単位則。 -/
lemma awData_unit_right {n : ℕ} (g : LinearData R x y n) :
    awData g (standardConstant (unitElement R x) n).val = g := by
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (awData g _).component J k hJ hk = g.component J k hJ hk
  rw [awData_component, Finset.sum_eq_single (⟨J.max' hJ, J.max'_mem hJ⟩ : J)]
  · exact awTerm_unit_right_max g J k hJ hk
  · intro j _ hj
    have hne : j.val ≠ J.max' hJ := fun he ↦ hj (Subtype.ext he)
    unfold awTerm
    rw [standardConstant_component_zero _ _ _ _ _ (AWIndex.right_two_of_ne_max hJ j.property hne)]
    exact DGNerve.compose_zero _ _
  · intro h
    exact (h (Finset.mem_univ _)).elim

end SerrePositivity.InfinityCategories.DoldKanComparison
