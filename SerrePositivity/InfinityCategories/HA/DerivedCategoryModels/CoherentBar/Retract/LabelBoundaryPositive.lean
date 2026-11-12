module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LabelNormalization
/-!
概要：正位置の Dold–Kan 境界を、零番面を除いた二つの有限和で記述する。
方針：Mathlib の Hσ と hσ の評価式を使い、零番面の二項を単体恒等式で相殺する。
規約：P の相殺・正規化証明を複製せず、Hσ の新しい有限和表示だけを証明する。
使われ方：実 bar の面境界と普遍ラベル係数の帰納段の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory CategoryTheory.Preadditive AlgebraicTopology AlgebraicTopology.DoldKan
open scoped _root_.Simplicial DoldKan
variable {C : Type v} [Category.{u} C] [Preadditive C] (X : SimplicialObject C)

lemma dgCoherentBarLabelBoundary_positive {n q a : ℕ} (hn : n = a + q) :
    (Hσ q : AlgebraicTopology.AlternatingFaceMapComplex.obj X ⟶ _).f (n + 1) =
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ (a + 1) • ((-1 : ℤ) ^ (i.val + 1) •
      (X.σ ⟨a + 1, by omega⟩ ≫ X.δ i.succ))) +
    ∑ i : Fin (n + 1), (-1 : ℤ) ^ a • ((-1 : ℤ) ^ (i.val + 1) •
      (X.δ i.succ ≫ X.σ ⟨a, by omega⟩)) := by
  have hd0 : X.σ (⟨a + 1, by omega⟩ : Fin (n + 2)) ≫ X.δ (0 : Fin (n + 3)) =
      X.δ (0 : Fin (n + 2)) ≫ X.σ (⟨a, by omega⟩ : Fin (n + 1)) := by
    have h := X.δ_comp_σ_of_le (i := (0 : Fin (n + 2))) (j := ⟨a, by omega⟩) (Fin.zero_le _)
    have hj : (⟨a, by omega⟩ : Fin (n + 1)).succ = (⟨a + 1, by omega⟩ : Fin (n + 2)) :=
      Fin.ext rfl
    rw [hj] at h
    simpa only [Fin.castSucc_zero] using h
  rw [Hσ, Homotopy.nullHomotopicMap'_f
    (c_mk (n + 2) (n + 1) rfl) (c_mk (n + 1) n rfl),
    hσ'_eq hn (c_mk (n + 1) n rfl),
    hσ'_eq (show n + 1 = (a + 1) + q by omega) (c_mk (n + 2) (n + 1) rfl)]
  simp only [eqToHom_refl, Category.comp_id, AlternatingFaceMapComplex.obj_d_eq,
    comp_zsmul, zsmul_comp, comp_sum, sum_comp, Finset.smul_sum]
  conv_lhs =>
    pattern (∑ i : Fin (n + 2), _)
    rw [Fin.sum_univ_succ]
  conv_lhs =>
    pattern (∑ i : Fin (n + 3), _)
    rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_succ]
  have hp : (-1 : ℤ) ^ (a + 1) = -((-1 : ℤ) ^ a) := by rw [pow_succ, mul_neg_one]
  have hsmul (b : ℤ) (f : X _⦋n + 1⦌ ⟶ X _⦋n + 1⦌) :
      b • ((-1 : ℤ) ^ a • f) = (-1 : ℤ) ^ a • (b • f) := smul_comm _ _ _
  rw [hd0, hp]
  simp only [neg_zsmul, smul_neg, hsmul]
  abel

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
