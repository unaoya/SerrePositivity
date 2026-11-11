module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedOperators
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarFaceDifferential
/-!
概要：元の面・退化ブロックを、始点を保つ単体写像の統一した係数入口と比較する。
方針：既存の端点輸送の異種等号と、同じシフト単位ブロックを介して同定する。
規約：既存の係数の定義・型は変更しない。
使われ方：元の正規化境界を始点を保つラベル作用へ展開する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

private lemma shiftBlock_degree_heq (a b : ℤ) (M : _root_.SerrePositivity.DifferentialGraded.RightModule R D) {q q' : ℤ}
    (hq : a + 0 - b = q) (hq' : a + 0 - b = q') :
    HEq (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D a b (_root_.SerrePositivity.DifferentialGraded.unitElement R M).val hq)
      (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D a b (_root_.SerrePositivity.DifferentialGraded.unitElement R M).val hq') := by
  have h : q = q' := hq.symm.trans hq'
  cases h
  rfl

lemma dgCoherentBarFaceBlock_based_heq {n : ℕ} (s : I _⦋n + 1⦌) (i : Fin (n + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock R D F s i)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F (SimplexCategory.δ i.succ) (by rfl) s) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock_heq R D F s i).trans
    ((shiftBlock_degree_heq R D ((n + 1 : ℕ) : ℤ) (n : ℤ)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, s⟩) (by omega) (by omega)).trans
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock_heq R D F (SimplexCategory.δ i.succ) (by rfl) s).symm)

lemma dgCoherentBarDegeneracyBlock_based_heq {n : ℕ} (s : I _⦋n⦌) (i : Fin (n + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracyBlock R D F s i)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F (SimplexCategory.σ i) (by
        simp [SimplexCategory.σ, Fin.predAboveOrderHom]) s) := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegeneracyBlock
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomTargetTransport R D _ _ _ _ _ _).property.trans
    ((shiftBlock_degree_heq R D (n : ℤ) ((n + 1 : ℕ) : ℤ)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩) (by omega) (by omega)).trans
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock_heq R D F (SimplexCategory.σ i) (by
        simp [SimplexCategory.σ, Fin.predAboveOrderHom]) s).symm)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
