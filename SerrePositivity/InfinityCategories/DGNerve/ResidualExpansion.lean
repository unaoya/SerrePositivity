module
public import SerrePositivity.InfinityCategories.DGNerve.CompositionCancellation

/-! # 方程式の微分の残差部分と純代数部分への展開

概要：各内部点の寄与の微分を、真部分集合の残差と右辺を使う二項に分ける。
方針：微分合成則と、微分が残差と右辺の和であることを用いる。
規約：HA Proposition 1.3.1.10。使われ方：主残差恒等式を残る有限和の相殺へ帰着する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.SimplexData

open DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：内部点での 真部分集合の残差を含む寄与。
方針：削除と左右切断のresidualを同じ次数へ合成し、元の符号を掛ける。
規約：HA Proposition 1.3.1.10。使われ方：微分した方程式の分解。 -/
def residualContribution {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    GradedHom A (s.obj a) (s.obj b) (k + 1 + 1) := by
  have hamin : IsLeast (I : Set (Fin (n + 1))) a := by rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (n + 1))) b := by rw [hb]; exact I.isGreatest_max' _
  have hE := Index.erase_two hamin.1 hbmax.1 haj hjb
  have hL := Index.left_two hamin.1 hj haj
  have hR := Index.right_two hj hbmax.1 hjb
  let fe := s.residual (I.erase j) a b (k + 1) hE
    (Index.erase_min hamin haj _) (Index.erase_max hbmax hjb _)
    (by have := Finset.card_erase_add_one hj; omega)
  let fl := s.hom (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ)) hL
    (Index.left_min hamin haj.le _) (Index.left_max hj _) rfl
  let fr := s.hom (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ)) hR
    (Index.right_min hj _) (Index.right_max hbmax hjb.le _) rfl
  let eL := s.residual (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ)) hL
    (Index.left_min hamin haj.le _) (Index.left_max hj _) rfl
  let eR := s.residual (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ)) hR
    (Index.right_min hj _) (Index.right_max hbmax hjb.le _) rfl
  exact Index.sign I j • (fe - compose A eR fl (by have := Index.split_card hj; omega) -
    (2 - ((I.filter (j ≤ ·)).card : ℤ)).negOnePow •
      compose A fr eL (by have := Index.split_card hj; omega))

/-- 概要：内部点での 真部分集合の右辺を含む純代数的な寄与。
方針：削除と左右切断のrhsを同じ次数へ合成し、元の符号を掛ける。
規約：HA Proposition 1.3.1.10。使われ方：微分した方程式の分解。 -/
def rhsContribution {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    GradedHom A (s.obj a) (s.obj b) (k + 1 + 1) := by
  have hamin : IsLeast (I : Set (Fin (n + 1))) a := by rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (n + 1))) b := by rw [hb]; exact I.isGreatest_max' _
  have hE := Index.erase_two hamin.1 hbmax.1 haj hjb
  have hL := Index.left_two hamin.1 hj haj
  have hR := Index.right_two hj hbmax.1 hjb
  let fe := s.rhs (I.erase j) a b (k + 1) hE
    (Index.erase_min hamin haj _) (Index.erase_max hbmax hjb _)
    (by have := Finset.card_erase_add_one hj; omega)
  let fl := s.hom (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ)) hL
    (Index.left_min hamin haj.le _) (Index.left_max hj _) rfl
  let fr := s.hom (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ)) hR
    (Index.right_min hj _) (Index.right_max hbmax hjb.le _) rfl
  let eL := s.rhs (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ)) hL
    (Index.left_min hamin haj.le _) (Index.left_max hj _) rfl
  let eR := s.rhs (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ)) hR
    (Index.right_min hj _) (Index.right_max hbmax hjb.le _) rfl
  exact Index.sign I j • (fe - compose A eR fl (by have := Index.split_card hj; omega) -
    (2 - ((I.filter (j ≤ ·)).card : ℤ)).negOnePow •
      compose A fr eL (by have := Index.split_card hj; omega))

/-- 概要：内部点の寄与の微分は、残差部分と真部分集合の右辺部分の和。
方針：Leibniz 則で展開し、微分と右辺の差である残差の定義を整理する。
規約：HA Proposition 1.3.1.10。使われ方：主残差恒等式を純代数部分の相殺へ分ける。 -/
lemma differential_term {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    differential A (s.term I a b k hI ha hb hk j hj haj hjb) =
      s.residualContribution I a b k hI ha hb hk j hj haj hjb +
        s.rhsContribution I a b k hI ha hb hk j hj haj hjb := by
  simp only [term, residualContribution, rhsContribution, residual,
    differential_units_smul, differential_sub, differential_compose,
    compose_sub_left, compose_sub_right, smul_sub, smul_add, Index.sign]
  abel

/-- 概要：右辺の微分は、全内部点の残差寄与の和と純代数寄与の和の和。
方針：微分を有限和へ分配し、各項の残差展開を適用する。
規約：HA Proposition 1.3.1.10。使われ方：純代数寄与の有限和が零であれば主残差恒等式となる。
純代数寄与の総和の零は、この定理の結論には含まない。 -/
lemma differential_rhs_expansion {n : ℕ} (s : SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    differential A (s.rhs I a b k hI ha hb hk) =
      (∑ j : I, if h : a < j.val ∧ j.val < b then
        s.residualContribution I a b k hI ha hb hk j.val j.property h.1 h.2 else 0) +
      ∑ j : I, if h : a < j.val ∧ j.val < b then
        s.rhsContribution I a b k hI ha hb hk j.val j.property h.1 h.2 else 0 := by
  unfold rhs
  rw [differential_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hint : a < j.val ∧ j.val < b
  · simp only [dite_eq_left hint]
    exact differential_term s I a b k hI ha hb hk j.val j.property hint.1 hint.2
  · simp only [dite_eq_right hint, differential, map_zero, add_zero]

end SerrePositivity.InfinityCategories.DGNerve.SimplexData
