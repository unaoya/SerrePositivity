module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedColumns
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.ShiftUnitIdentity
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.GradedStages
/-!
概要：恒等単体写像の実列は、実 bar の単位列と異種等号で一致する。
方針：同じシフトの単位ブロックへ戻し、単体ラベルの恒等写像則を直和包含に適用する。
規約：零次数と差の形の次数の比較を明示する。
使われ方：有限段階の普遍係数比較の初期段。
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

lemma dgCoherentBarBasedIdentityColumn_heq {n : ℕ} (s : I _⦋n⦌) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedColumn R D F (𝟙 ⦋n⦌) rfl s)
      ((eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) ⟨n, s⟩)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f 0
        (unitElement R (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).val) := by
  let M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩
  have hblock := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock_heq R D F (𝟙 ⦋n⦌) rfl s).trans
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgBarRetractShiftBlock_heq R D M M M M rfl rfl
      (n : ℤ) (n : ℤ) (n : ℤ) (n : ℤ) rfl rfl rfl (sub_self (n : ℤ))
      (_root_.SerrePositivity.DifferentialGraded.unitElement R M).val (_root_.SerrePositivity.DifferentialGraded.unitElement R M).val HEq.rfl
      (by omega : (n : ℤ) + 0 - (n : ℤ) = (n : ℤ) - (n : ℤ))
      (by omega : (n : ℤ) + 0 - (n : ℤ) = 0)).trans
        (heq_of_eq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgBarRetractShiftBlock_unit R D (n : ℤ) M)))
  have hlabel : (⟨n, I.map (𝟙 ⦋n⦌).op s⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) = ⟨n, s⟩ :=
    congrArg (fun t => (⟨n, t⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I))
      (ConcreteCategory.congr_hom (I.map_id (Opposite.op ⦋n⦌)) s)
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarPostInclusion_heq_of_degrees R D F ⟨n, s⟩
    ⟨n, I.map (𝟙 ⦋n⦌).op s⟩ ⟨n, s⟩ hlabel (sub_self (n : ℤ))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedBlock R D F (𝟙 ⦋n⦌) rfl s)
    (unitElement R (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))).val
    hblock
  exact h.trans (heq_of_eq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarUnit_restrict R D F ⟨n, s⟩).symm)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
