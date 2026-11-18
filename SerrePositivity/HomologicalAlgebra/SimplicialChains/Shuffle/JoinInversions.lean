module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.SignInversions
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.EdgeJoinCounts
public import Mathlib.Algebra.BigOperators.Fin

/-!
# 経路の連結の逆転数

概要：Berger–Fresse §1.1.4 の連結における逆転数の加法公式を証明する。
方針：水平辺を前半・後半に分け、後半の各水平辺に前半の垂直辺数を加える。
規約：交差する対の数は「前半の垂直辺数 × 後半の水平辺数」。
使われ方：切断の Koszul 符号を signature の積から取り出す。
-/

@[expose] public section

namespace SerrePositivity.SimplicialChains.Shuffle

private lemma inversionNumber_eq_sum {N : ℕ} (S : Finset (Fin N)) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.inversionNumber S = ∑ j : Fin N,
      if j ∈ S then (Sᶜ.filter (fun i => i.val < j.val)).card else 0 := by
  have he : S = Finset.univ.filter (fun j => j ∈ S) := by ext j; simp
  unfold _root_.SerrePositivity.SimplicialChains.Shuffle.inversionNumber
  conv_lhs => arg 1; rw [he]
  rw [Finset.sum_filter]

/-- 概要：辺集合の連結の逆転数の公式（Berger–Fresse §1.1.4）。
方針：全水平辺の和を二つの有限順序に分け、接頭垂直辺数の公式を適用する。
規約：全長の等式 h による移送を含み、零長でも成立する。
使われ方：前後経路の signature の積と Koszul 符号。 -/
lemma inversionNumber_edgeJoin {a b N : ℕ}
    (S : Finset (Fin a)) (T : Finset (Fin b)) (h : a + b = N) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.inversionNumber (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T h) =
      _root_.SerrePositivity.SimplicialChains.Shuffle.inversionNumber S + _root_.SerrePositivity.SimplicialChains.Shuffle.inversionNumber T + (a - S.card) * T.card := by
  subst N
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.inversionNumber_eq_sum, Fin.sum_univ_add]
  have hf (j : Fin a) :
      (if Fin.castAdd b j ∈ _root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T rfl then
        ((_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T rfl)ᶜ.filter (fun i => i.val < (Fin.castAdd b j).val)).card else 0) =
      if j ∈ S then (Sᶜ.filter (fun i => i.val < j.val)).card else 0 := by
    have hm : Fin.castAdd b j ∈ _root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T rfl ↔ j ∈ S := by
      simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.mem_edgeJoin, Fin.val_castAdd, dite_eq_left j.isLt]
    simp only [hm, _root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin_compl, Fin.val_castAdd,
      _root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin_prefix_card_front Sᶜ Tᶜ rfl j.val (Nat.le_of_lt j.isLt)]
  have hb (j : Fin b) :
      (if Fin.natAdd a j ∈ _root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T rfl then
        ((_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T rfl)ᶜ.filter (fun i => i.val < (Fin.natAdd a j).val)).card else 0) =
      if j ∈ T then (a - S.card) + (Tᶜ.filter (fun i => i.val < j.val)).card else 0 := by
    have hm : Fin.natAdd a j ∈ _root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin S T rfl ↔ j ∈ T := by
      simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.mem_edgeJoin, Fin.val_natAdd]
      rw [dite_eq_right (show ¬a + j.val < a by omega)]
      simp
    simp only [hm, _root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin_compl, Fin.val_natAdd,
      _root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin_prefix_card_back Sᶜ Tᶜ rfl j.val (Nat.le_of_lt j.isLt),
      Finset.card_compl, Fintype.card_fin]
  simp_rw [hf, hb]
  rw [← _root_.SerrePositivity.SimplicialChains.Shuffle.inversionNumber_eq_sum S]
  have he : (∑ j : Fin b, if j ∈ T then
      (a - S.card) + (Tᶜ.filter (fun i => i.val < j.val)).card else 0) =
      (a - S.card) * T.card + _root_.SerrePositivity.SimplicialChains.Shuffle.inversionNumber T := by
    rw [← Finset.sum_filter]
    have hfilter : Finset.univ.filter (fun j => j ∈ T) = T := by ext j; simp
    rw [hfilter, Finset.sum_add_distrib, Finset.sum_const]
    simp only [smul_eq_mul, Nat.mul_comm]
    rfl
  rw [he]
  omega

end SerrePositivity.SimplicialChains.Shuffle
