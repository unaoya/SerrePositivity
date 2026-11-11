module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.FullSimplexSigns
/-!
概要：最後の切断補正を含む内部パラメーター和を、全標準面の符号付き和へまとめる。
方針：最後の内部頂点の符号が −1 であることと、有限和の最終項の分離を使う。
規約：加法可換群の整数単位スカラーだけを使う。
使われ方：余錐族の HA 右辺から全パラメーター面の境界を取り出す。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar

lemma dgCoherentBarParameter_boundary_sum {V : Type*} [AddCommGroup V]
    (m : ℕ) (a : Fin (m + 2) → V) :
    (∑ j : Fin (m + 1), (((m + 1 : ℕ) : ℤ) - (j.val : ℤ)).negOnePow •
      (a j.castSucc - if j = Fin.last m then a (Fin.last (m + 1)) else 0)) =
      ∑ i : Fin (m + 2), (((m + 1 : ℕ) : ℤ) - (i.val : ℤ)).negOnePow • a i := by
  classical
  have hs : (((m + 1 : ℕ) : ℤ) - ((Fin.last m).val : ℤ)).negOnePow = (-1 : ℤˣ) := by
    rw [show ((m + 1 : ℕ) : ℤ) - ((Fin.last m).val : ℤ) = 1 by
      simp only [Fin.val_last, Nat.cast_add, Nat.cast_one]; omega]
    exact Int.negOnePow_one
  rw [Fin.sum_univ_castSucc
    (fun i : Fin (m + 2) => (((m + 1 : ℕ) : ℤ) - (i.val : ℤ)).negOnePow • a i)]
  simp only [smul_sub, smul_ite, smul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_eq_left, Fin.val_castSucc]
  rw [hs]
  simp only [Fin.val_last, sub_self, Int.negOnePow_zero, one_smul, Units.smul_def,
    Units.val_neg, Units.val_one, neg_one_zsmul, sub_neg_eq_add]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
