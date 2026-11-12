module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedEndColumnAction
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BoundaryFaceTerms
/-!
概要：退化の後の面による実境界項は、始点保存の単体自己写像の零次数作用である。
方針：元の面列と退化ブロックを既存の始点保存比較へ渡し、列の合成則で一つにする。
規約：同じ実 Hom と零次数への線形移送を使う。
使われ方：実境界の第一面和を、普遍ラベル係数の有限和へ戻す。
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

lemma dgCoherentBarFaceLeftTerm_based {n : ℕ} (s : I _⦋n⦌) (q : ℕ) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarFaceLeftTerm R D F s q i =
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedEndColumn R D F
      (SimplexCategory.δ i.succ ≫ SimplexCategory.σ ⟨n - q, by omega⟩) (by
        change (SimplexCategory.σ (⟨n - q, by omega⟩ : Fin (n + 1))).toOrderHom
          ((SimplexCategory.δ i.succ).toOrderHom 0) = 0
        have hd : (SimplexCategory.δ i.succ).toOrderHom 0 = 0 := by
          simp [SimplexCategory.δ, Fin.succAboveOrderEmb, Fin.succAbove]
        rw [hd]
        simp [SimplexCategory.σ, Fin.predAboveOrderHom]) s := by
  let j : Fin (n + 1) := ⟨n - q, by omega⟩
  have hσ : (SimplexCategory.σ j).toOrderHom 0 = 0 := by
    simp [SimplexCategory.σ, Fin.predAboveOrderHom]
  have hδ : (SimplexCategory.δ i.succ).toOrderHom 0 = 0 := by
    simp [SimplexCategory.δ, Fin.succAboveOrderEmb, Fin.succAbove]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) (D := RightModule R D)
    rfl rfl rfl
    (by omega : (-1 : ℤ) = (n : ℤ) - ((n + 1 : ℕ) : ℤ))
    (by omega : (1 : ℤ) = ((n + 1 : ℕ) : ℤ) - (n : ℤ))
    (by omega : (0 : ℤ) = (n : ℤ) - (n : ℤ))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D F (I.σ j s) i) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracyBlock R D F s j)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumn R D F (SimplexCategory.δ i.succ) hδ (I.σ j s))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F (SimplexCategory.σ j) hσ s)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarFaceColumn_based_heq R D F (I.σ j s) i)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarDegeneracyBlock_based_heq R D F s j) rfl (by omega)
  have hc := h.trans (heq_of_eq
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumn_comp R D F (SimplexCategory.σ j) hσ
      (SimplexCategory.δ i.succ) hδ s))
  exact eq_of_heq (hc.trans (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedEndColumn_heq R D F
    (SimplexCategory.δ i.succ ≫ SimplexCategory.σ j) (by
      change (SimplexCategory.σ j).toOrderHom ((SimplexCategory.δ i.succ).toOrderHom 0) = 0
      rw [hδ, hσ]) s).symm)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
