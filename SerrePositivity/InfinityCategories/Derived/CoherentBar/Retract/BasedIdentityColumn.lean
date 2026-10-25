module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedColumns
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.ShiftUnitIdentity
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.GradedStages
/-!
概要：恒等単体写像の実列は、実 bar の単位列と異種等号で一致する。
方針：同じシフトの単位ブロックへ戻し、単体ラベルの恒等写像則を直和包含に適用する。
規約：零次数と差の形の次数の比較を明示する。
使われ方：有限段階の普遍係数比較の初期段。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarBasedIdentityColumn_heq {n : ℕ} (s : I _⦋n⦌) :
    HEq (dgCoherentBarBasedColumn R D F (𝟙 ⦋n⦌) rfl s)
      ((eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) ⟨n, s⟩)
        (dgCoherentBarGraded R D F)).f 0
        (unitElement R (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).val) := by
  let M := dgCoherentBarSource R D F ⟨n, s⟩
  have hblock := (dgCoherentBarBasedBlock_heq R D F (𝟙 ⦋n⦌) rfl s).trans
    ((dgBarRetractShiftBlock_heq R D M M M M rfl rfl
      (n : ℤ) (n : ℤ) (n : ℤ) (n : ℤ) rfl rfl rfl (sub_self (n : ℤ))
      (unitElement R M).val (unitElement R M).val HEq.rfl
      (by omega : (n : ℤ) + 0 - (n : ℤ) = (n : ℤ) - (n : ℤ))
      (by omega : (n : ℤ) + 0 - (n : ℤ) = 0)).trans
        (heq_of_eq (dgBarRetractShiftBlock_unit R D (n : ℤ) M)))
  have hlabel : (⟨n, I.map (𝟙 ⦋n⦌).op s⟩ : dgCoherentBarIndex I) = ⟨n, s⟩ :=
    congrArg (fun t => (⟨n, t⟩ : dgCoherentBarIndex I))
      (ConcreteCategory.congr_hom (I.map_id (Opposite.op ⦋n⦌)) s)
  have h := dgCoherentBarPostInclusion_heq_of_degrees R D F ⟨n, s⟩
    ⟨n, I.map (𝟙 ⦋n⦌).op s⟩ ⟨n, s⟩ hlabel (sub_self (n : ℤ))
    (dgCoherentBarBasedBlock R D F (𝟙 ⦋n⦌) rfl s)
    (unitElement R (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))).val
    hblock
  exact h.trans (heq_of_eq (dgCoherentBarUnit_restrict R D F ⟨n, s⟩).symm)

end SerrePositivity.InfinityCategories
