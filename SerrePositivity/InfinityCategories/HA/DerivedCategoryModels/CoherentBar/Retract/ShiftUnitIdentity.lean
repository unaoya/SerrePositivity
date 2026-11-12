module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BlockTransport
/-!
概要：同じシフト間の単位ブロックはシフト後の加群の単位そのものである。
方針：中間の元の加群の単位を消し、既存のシフト射影・包含の逆関係を使う。
規約：実 Hom の厳密な等式を用い、ホモトピー単位に弱めない。
使われ方：始点保存の次数零ラベル作用を通常の直和射と照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgBarRetractShiftBlock_unit (s : ℤ) (M : _root_.SerrePositivity.DifferentialGraded.RightModule R D) :
    _root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D s s (unitElement R M).val (by omega : s + 0 - s = 0) =
      (_root_.SerrePositivity.DifferentialGraded.unitElement R (shiftModule s M)).val := by
  have hu := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.unit_compose_of_heq (A := R) (D := _root_.SerrePositivity.DifferentialGraded.RightModule R D)
    (_root_.SerrePositivity.DifferentialGraded.unitElement R M).val (_root_.SerrePositivity.DifferentialGraded.moduleShiftOutElement R D s M) rfl rfl rfl HEq.rfl
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) (D := RightModule R D)
    rfl rfl rfl (add_zero s) rfl (rfl : (0 : ℤ) = 0)
    (moduleShiftInElement R D s M)
    (compose R (x := shiftModule s M) (y := M) (z := M)
      (unitElement R M).val (moduleShiftOutElement R D s M) rfl)
    (moduleShiftInElement R D s M) (moduleShiftOutElement R D s M)
    HEq.rfl hu (by omega : (s + 0) + -s = 0) (add_neg_cancel s)
  exact eq_of_heq (hc.trans (heq_of_eq (moduleShiftOutIn R D s M)))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
