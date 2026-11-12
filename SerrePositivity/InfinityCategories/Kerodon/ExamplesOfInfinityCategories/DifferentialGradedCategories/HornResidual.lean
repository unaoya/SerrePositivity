module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Bianchi
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornFilling

/-! # 内部ホーンの欠けた面の方程式

概要：充填候補の欠けた面の残差は零となる。
方針：主残差恒等式を全体集合に適用し、既知の全ての面と左右切断の残差を除く。
規約：HA Proposition 1.3.1.10。使われ方：前提なしの内部ホーン充填を完成する。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

namespace SimplexData

/-- 概要：一集合の方程式が成り立つなら、その集合の各成分の残差は零。
方針：残差の零と方程式の同値を使う。
規約：HA Proposition 1.3.1.10。使われ方：既知の面や切断の残差の消去。 -/
lemma residual_zero_of_equation {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (h : s.Equation I)
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) : s.residual I a b k hI ha hb hk = 0 :=
  (s.residual_eq_zero_iff I a b k hI ha hb hk).mpr (h a b k hI ha hb hk)

/-- 概要：左右切断の方程式が成り立つとき、残差寄与は削除集合の符号付き残差だけになる。
方針：左右切断の残差を零とし、零との合成を消去する。
規約：HA Proposition 1.3.1.10。使われ方：ホーンの欠けた面の残差の抽出。 -/
lemma residualContribution_of_cuts {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b)
    (hL : s.Equation (I.filter (· ≤ j))) (hR : s.Equation (I.filter (j ≤ ·))) :
    s.residualContribution I a b k hI ha hb hk j hj haj hjb = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
      s.residual (I.erase j) a b (k + 1)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two (ha ▸ I.min'_mem _) (hb ▸ I.max'_mem _) haj hjb)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_min (by rw [ha]; exact I.isLeast_min' _) haj _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_max (by rw [hb]; exact I.isGreatest_max' _) hjb _)
        (by have := Finset.card_erase_add_one hj; omega) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.residualContribution, residual_zero_of_equation s _ hL,
    residual_zero_of_equation s _ hR, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, sub_zero]

end SimplexData

namespace HornData

/-- 概要：充填候補は欠けた面自身の方程式も満たす。
方針：全体集合の主残差恒等式と微分の二乗零から、唯一残る符号付き残差を取り出す。
規約：HA Proposition 1.3.1.10。使われ方：充填候補を前提なしに単体へ昇格する。 -/
lemma fillerData_missing_equation {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (h0 : 0 < i) (hlast : i < Fin.last (n + 2)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fillerData σ h0 hlast).Equation (Finset.univ.erase i) := by
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fillerData σ h0 hlast
  let V : Finset (Fin (n + 3)) := Finset.univ
  let k : ℤ := 2 - (V.card : ℤ)
  have hV : 2 ≤ V.card := by simp [V]
  have ha : (0 : Fin (n + 3)) = V.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hV) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.univ_min_zero n _
  have hb : Fin.last (n + 2) = V.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hV) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.univ_max_last n _
  have hi : i ∈ V := Finset.mem_univ i
  have hcuts : ∀ j : Fin (n + 3), 0 < j → j < Fin.last (n + 2) →
      s.Equation (V.filter (· ≤ j)) ∧ s.Equation (V.filter (j ≤ ·)) := by
    intro j hj0 hjlast
    have hL : V.filter (· ≤ j) ≠ Finset.univ ∧
        V.filter (· ≤ j) ≠ Finset.univ.erase i := by
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.exists_covering_face _ i).mp
      refine ⟨Fin.last (n + 2), ne_of_gt hlast, ?_⟩
      simp only [Finset.mem_filter, not_and]
      intro _
      exact not_le_of_gt hjlast
    have hR : V.filter (j ≤ ·) ≠ Finset.univ ∧
        V.filter (j ≤ ·) ≠ Finset.univ.erase i := by
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.exists_covering_face _ i).mp
      refine ⟨0, ne_of_lt h0, ?_⟩
      simp only [Finset.mem_filter, not_and]
      intro _
      exact not_le_of_gt hj0
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fillerData_known_equation σ h0 hlast _ hL.1 hL.2,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fillerData_known_equation σ h0 hlast _ hR.1 hR.2⟩
  have hsum :
      (∑ j : V, if h : 0 < j.val ∧ j.val < Fin.last (n + 2) then
        s.residualContribution V 0 (Fin.last (n + 2)) k hV ha hb rfl
          j.val j.property h.1 h.2 else 0) = 0 := by
    rw [← s.bianchi V 0 (Fin.last (n + 2)) k hV ha hb rfl]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fillerData_top_equation σ h0 hlast 0 (Fin.last (n + 2)) k hV ha hb rfl]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_squared _
  have hsingle :
      (∑ j : V, if h : 0 < j.val ∧ j.val < Fin.last (n + 2) then
        s.residualContribution V 0 (Fin.last (n + 2)) k hV ha hb rfl
          j.val j.property h.1 h.2 else 0) =
      s.residualContribution V 0 (Fin.last (n + 2)) k hV ha hb rfl i hi h0 hlast := by
    rw [Finset.sum_eq_single (⟨i, hi⟩ : V)]
    · simp only [dite_eq_left (show 0 < i ∧ i < Fin.last (n + 2) from ⟨h0, hlast⟩)]
    · intro j _ hji
      by_cases hint : 0 < j.val ∧ j.val < Fin.last (n + 2)
      · rw [dite_eq_left hint, s.residualContribution_of_cuts V 0 (Fin.last (n + 2)) k
          hV ha hb rfl j.val j.property hint.1 hint.2
          (hcuts j.val hint.1 hint.2).1 (hcuts j.val hint.1 hint.2).2]
        have hji' : j.val ≠ i := fun h => hji (Subtype.ext h)
        have hknown := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.exists_covering_face (V.erase j.val) i).mp
          ⟨j.val, hji', Finset.notMem_erase j.val V⟩
        rw [s.residual_zero_of_equation _
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fillerData_known_equation σ h0 hlast _ hknown.1 hknown.2)]
        exact smul_zero _
      · simp only [dite_eq_right hint]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  rw [hsingle, s.residualContribution_of_cuts V 0 (Fin.last (n + 2)) k hV ha hb rfl i hi h0 hlast
    (hcuts i h0 hlast).1 (hcuts i h0 hlast).2] at hsum
  have hz := congrArg (fun z => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign V i • z) hsum
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign, smul_smul, Int.units_mul_self, one_smul, smul_zero] at hz
  have heq := (s.residual_eq_zero_iff (V.erase i) 0 (Fin.last (n + 2)) (k + 1)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two (ha ▸ V.min'_mem _) (hb ▸ V.max'_mem _) h0 hlast)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_min (by rw [ha]; exact V.isLeast_min' _) h0 _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_max (by rw [hb]; exact V.isGreatest_max' _) hlast _)
    (by have := Finset.card_erase_add_one hi; omega)).mp hz
  intro a b q hM haM hbM hq
  have ha0 : a = 0 := haM.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_min (by rw [ha]; exact V.isLeast_min' _) h0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM)).symm
  have hbLast : b = Fin.last (n + 2) := hbM.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_max (by rw [hb]; exact V.isGreatest_max' _) hlast (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM)).symm
  have hqk : q = k + 1 := by
    have hc := Finset.card_erase_add_one hi
    have hq' : q = 2 - ((V.erase i).card : ℤ) := hq
    dsimp only [k]
    omega
  subst ha0
  subst hbLast
  subst hqk
  exact heq

end HornData

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
