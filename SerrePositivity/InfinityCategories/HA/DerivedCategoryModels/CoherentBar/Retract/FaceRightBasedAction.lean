module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.FaceLeftBasedAction
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.FaceHomotopyAction
/-!
概要：面の後の退化による実境界項を、始点保存の自己写像の符号付き零次数作用へ移す。
方針：面上のホモトピー列を制限し、面ブロック・退化列と単体写像の合成則を使う。
規約：段階が面の次数以下の場合だけ作用式を使い、他の場合は既存の消滅式を使う。
使われ方：実境界の第二面和を普遍ラベル係数の有限和へ戻す。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarFaceRightTerm_based {n : ℕ} (s : I _⦋n + 1⦌)
    (q : ℕ) (hq : q ≤ n) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarFaceRightTerm R D F s q i =
    ((q : ℤ) + 1).negOnePow • _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedEndColumn R D F
      (SimplexCategory.σ ⟨n - q, by omega⟩ ≫ SimplexCategory.δ i.succ) (by
        change (SimplexCategory.δ i.succ).toOrderHom
          ((SimplexCategory.σ (⟨n - q, by omega⟩ : Fin (n + 1))).toOrderHom 0) = 0
        have hσ : (SimplexCategory.σ (⟨n - q, by omega⟩ : Fin (n + 1))).toOrderHom 0 = 0 := by
          simp [SimplexCategory.σ, Fin.predAboveOrderHom]
        rw [hσ]
        simp [SimplexCategory.δ, Fin.succAboveOrderEmb, Fin.succAbove]) s := by
  let j : Fin (n + 1) := ⟨n - q, by omega⟩
  have hσ : (SimplexCategory.σ j).toOrderHom 0 = 0 := by
    simp [SimplexCategory.σ, Fin.predAboveOrderHom]
  have hδ : (SimplexCategory.δ i.succ).toOrderHom 0 = 0 := by
    simp [SimplexCategory.δ, Fin.succAboveOrderEmb, Fin.succAbove]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) (D := RightModule R D)
    rfl rfl rfl
    (by omega : (1 : ℤ) = ((n + 1 : ℕ) : ℤ) - (n : ℤ))
    (by omega : (-1 : ℤ) = (n : ℤ) - ((n + 1 : ℕ) : ℤ))
    (by omega : (0 : ℤ) = ((n + 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracyColumn R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace s i.succ).2 j)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock R D F s i)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumn R D F (SimplexCategory.σ j) hσ (I.δ i.succ s))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F (SimplexCategory.δ i.succ) hδ s)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarDegeneracyColumn_based_heq R D F (I.δ i.succ s) j)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarFaceBlock_based_heq R D F s i) rfl (by omega)
  have hc := h.trans (heq_of_eq
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumn_comp R D F (SimplexCategory.δ i.succ) hδ
      (SimplexCategory.σ j) hσ s))
  have he := eq_of_heq (hc.trans (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedEndColumn_heq R D F
    (SimplexCategory.σ j ≫ SimplexCategory.δ i.succ) (by
      change (SimplexCategory.δ i.succ).toOrderHom ((SimplexCategory.σ j).toOrderHom 0) = 0
      rw [hσ, hδ]) s).symm)
  exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarFaceRightTerm_action R D F s q hq i).trans
    (congrArg (fun z => ((q : ℤ) + 1).negOnePow • z) he)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
