module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LabelNormalization
/-!
概要：Dold–Kan 境界の最後の段と、単体次数を超える段の面表示を与える。
方針：Mathlib の hσ 評価式を使い、最後の段では最初の二つの単位面を相殺する。
規約：既存の P・PInfty の証明は直接利用し、相殺計算は新しい面表示に限る。
使われ方：実境界の最後の段・安定段と普遍ラベル係数の照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
  AlgebraicTopology AlgebraicTopology.DoldKan
open scoped _root_.Simplicial DoldKan
variable {C : Type v} [Category.{u} C] [Preadditive C] (X : SimplicialObject C)

lemma dgCoherentBarLabelBoundary_last (n : ℕ) :
    (Hσ (n + 1) : AlternatingFaceMapComplex.obj X ⟶ _).f (n + 1) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i.val + 2) •
        (X.σ (0 : Fin (n + 2)) ≫ X.δ i.succ.succ) := by
  have h0 : X.σ (0 : Fin (n + 2)) ≫ X.δ (0 : Fin (n + 3)) = 𝟙 _ := by
    simpa only [Fin.castSucc_zero] using X.δ_comp_σ_self (i := (0 : Fin (n + 2)))
  have h1 := X.δ_comp_σ_succ (i := (0 : Fin (n + 2)))
  rw [Hσ, Homotopy.nullHomotopicMap'_f
    (c_mk (n + 2) (n + 1) rfl) (c_mk (n + 1) n rfl),
    hσ'_eq_zero (by omega : n < n + 1) (c_mk (n + 1) n rfl),
    hσ'_eq (show n + 1 = 0 + (n + 1) from (Nat.zero_add _).symm)
      (c_mk (n + 2) (n + 1) rfl)]
  simp only [eqToHom_refl, Category.comp_id, pow_zero, one_zsmul, comp_zero, zero_add,
    AlternatingFaceMapComplex.obj_d_eq, comp_sum, comp_zsmul, Fin.mk_zero]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, pow_zero, pow_one, one_zsmul, neg_zsmul, h0, h1,
    Nat.add_assoc, zero_add, add_neg_cancel_left]

lemma dgCoherentBarLabelBoundary_above {n q : ℕ} (hq : n + 1 < q) :
    (Hσ q : AlternatingFaceMapComplex.obj X ⟶ _).f (n + 1) = 0 := by
  rw [Hσ, Homotopy.nullHomotopicMap'_f
    (c_mk (n + 2) (n + 1) rfl) (c_mk (n + 1) n rfl),
    hσ'_eq_zero (by omega : n < q) (c_mk (n + 1) n rfl),
    hσ'_eq_zero hq (c_mk (n + 2) (n + 1) rfl), comp_zero, zero_comp, add_zero]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
