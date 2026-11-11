module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LabelNormalization
/-!
概要：Mathlib の段階的ラベル射影を、始点を保つ面と退化だけの式で評価する。
方針：P_succ と HigherFacesVanish の既存 Hσ 計算を直接使う。
規約：Mathlib の射影や相殺証明をコピーしない。実 bar との比較は別に行う。
使われ方：ラベル係数の始点支持と、実正規化作用素の安定化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory CategoryTheory.Preadditive AlgebraicTopology AlgebraicTopology.DoldKan
open scoped _root_.Simplicial DoldKan
variable (R : Type u) [CommRing R] (I : SSet.{u})

def dgCoherentBarLabelStage (q : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelComplex R I ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelComplex R I := P q

lemma dgCoherentBarLabelStage_succ_f {n q a : ℕ} (ha : n = a + q) :
    (dgCoherentBarLabelStage R I (q + 1)).f (n + 1) =
    (dgCoherentBarLabelStage R I q).f (n + 1) -
      ((dgCoherentBarLabelStage R I q).f (n + 1) ≫
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelModule R I).δ ⟨a + 1, by omega⟩ ≫
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelModule R I).σ ⟨a, by omega⟩ :
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelComplex R I).X (n + 1) ⟶
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarLabelComplex R I).X (n + 1)) := by
  simp only [dgCoherentBarLabelStage, P_succ, HomologicalComplex.comp_f,
    HomologicalComplex.add_f_apply, comp_add, Category.comp_id]
  rw [(HigherFacesVanish.of_P q n).comp_Hσ_eq ha]
  exact (sub_eq_add_neg _ _).symm

lemma dgCoherentBarLabelStage_stable_f {n q : ℕ} (hq : n < q) :
    (dgCoherentBarLabelStage R I (q + 1)).f (n + 1) =
      (dgCoherentBarLabelStage R I q).f (n + 1) := by
  simp only [dgCoherentBarLabelStage, P_succ, HomologicalComplex.comp_f,
    HomologicalComplex.add_f_apply, comp_add, Category.comp_id]
  rw [(HigherFacesVanish.of_P q n).comp_Hσ_eq_zero hq, add_zero]

lemma dgCoherentBarLabelStage_zero_f (q : ℕ) :
    (dgCoherentBarLabelStage R I q).f 0 = 𝟙 _ := P_f_0_eq q

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
