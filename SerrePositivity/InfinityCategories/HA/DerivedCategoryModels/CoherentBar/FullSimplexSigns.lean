module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.FullSimplexRhs
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarSubsetCuts
/-!
概要：全体 HA 右辺を二区間へ分けた際の符号を計算する。
方針：内部頂点の右側の濃度を既存の tail の濃度公式で求める。
規約：元の単体側にはパラメーター次数の符号だけが加わる。
使われ方：高次 Hom の Leibniz 項とパラメーターの面の有限和の符号照合。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar

lemma dgCoherentBarFullTerm_sign_card (n : ℕ) (i : Fin n) :
    ((Finset.univ : Finset (Fin (n + 2))).filter (i.succ.castSucc < ·)).card =
      n - i.val := by
  have hf : (Finset.univ : Finset (Fin (n + 2))).filter (i.succ.castSucc < ·) =
      Finset.univ.filter (i.succ.succ ≤ ·) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.castSucc_lt_iff_succ_le
  rw [hf, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail_card (n + 1) i.succ.succ]
  have := i.isLt
  simp only [Fin.val_succ]
  omega

lemma dgCoherentBarFullTerm_sign (n : ℕ) (i : Fin n) :
    (((Finset.univ : Finset (Fin (n + 2))).filter (i.succ.castSucc < ·)).card : ℤ).negOnePow =
      ((n : ℤ) - (i.val : ℤ)).negOnePow := by
  rw [dgCoherentBarFullTerm_sign_card]
  congr 1
  have := i.isLt
  omega

lemma dgCoherentBarFullTerm_sign_left (n m : ℕ) (i : Fin n) :
    (((Finset.univ : Finset (Fin (n + m + 2))).filter
      ((i.castAdd m).succ.castSucc < ·)).card : ℤ).negOnePow =
      (m : ℤ).negOnePow *
        (((Finset.univ : Finset (Fin (n + 2))).filter
          (i.succ.castSucc < ·)).card : ℤ).negOnePow := by
  rw [dgCoherentBarFullTerm_sign, dgCoherentBarFullTerm_sign, ← Int.negOnePow_add]
  congr 1
  simp only [Nat.cast_add, Fin.val_castAdd]
  omega

lemma dgCoherentBarFullTerm_sign_right (n m : ℕ) (j : Fin m) :
    (((Finset.univ : Finset (Fin (n + m + 2))).filter
      ((j.natAdd n).succ.castSucc < ·)).card : ℤ).negOnePow =
      (((Finset.univ : Finset (Fin (m + 2))).filter
        (j.succ.castSucc < ·)).card : ℤ).negOnePow := by
  rw [dgCoherentBarFullTerm_sign, dgCoherentBarFullTerm_sign]
  congr 1
  simp only [Nat.cast_add, Fin.val_natAdd]
  omega

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
