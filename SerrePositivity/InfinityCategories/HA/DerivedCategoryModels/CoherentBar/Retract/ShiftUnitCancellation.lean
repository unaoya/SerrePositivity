module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.ShiftUnitIdentity
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut
/-!
概要：単位のシフトブロックによる前合成は全斉次 Hom の零性を反映する。
方針：逆向きのシフト単位を合成し、厳密な合成則から単位へ戻す。
規約：ホモトピー圏の可逆性で代用せず、元の全 Hom 上で消去する。
使われ方：普遍係数列の退化ブロック合成後の消滅から、列自体の消滅を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgBarRetractShiftUnit_inverse (s t : ℤ) (M : _root_.SerrePositivity.DifferentialGraded.RightModule R D) :
    _root_.SerrePositivity.DifferentialGraded.compose R (x := shiftModule t M) (y := shiftModule s M) (z := shiftModule t M)
      (moduleHomShiftBlock R D s t (unitElement R M).val (by omega : s + 0 - t = s - t))
      (moduleHomShiftBlock R D t s (unitElement R M).val (by omega : t + 0 - s = t - s))
      (by omega : (t - s) + (s - t) = 0) =
      (_root_.SerrePositivity.DifferentialGraded.unitElement R (shiftModule t M)).val := by
  have h := _root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock_comp R D t s t (unitElement R M).val (unitElement R M).val
    (by omega : t + 0 - s = t - s) (by omega : s + 0 - t = s - t)
    (by omega : (t - s) + (s - t) = 0)
  rw [unit_compose] at h
  exact h.trans (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgBarRetractShiftBlock_unit R D t M)

lemma dgBarRetractShiftUnit_precompose_zero {s t q k : ℤ}
    (M N : _root_.SerrePositivity.DifferentialGraded.RightModule R D) (f : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (shiftModule t M) N).X q)
    (hk : (s - t) + q = k)
    (hf : _root_.SerrePositivity.DifferentialGraded.compose R (x := shiftModule s M) (y := shiftModule t M) (z := N) f
      (moduleHomShiftBlock R D s t (unitElement R M).val (by omega : s + 0 - t = s - t))
      hk = 0) : f = 0 := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum (A := R) (D := _root_.SerrePositivity.DifferentialGraded.RightModule R D)
    (w := _root_.SerrePositivity.DifferentialGraded.shiftModule t M) (x := _root_.SerrePositivity.DifferentialGraded.shiftModule s M) (y := _root_.SerrePositivity.DifferentialGraded.shiftModule t M) (z := N)
    (p := t - s) (q := s - t) (r := q) (a := 0) (b := k) (t := q)
    (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D t s (unitElement R M).val (by omega : t + 0 - s = t - s))
    (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D s t (unitElement R M).val (by omega : s + 0 - t = s - t))
    f (by omega) hk (zero_add q)
  rw [dgBarRetractShiftUnit_inverse R D s t M, compose_unit, hf, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose] at h
  exact h

lemma dgBarRetractShiftUnit_transport_precompose_zero (s t : ℤ)
    (M N P : _root_.SerrePositivity.DifferentialGraded.RightModule R D) (hN : N = _root_.SerrePositivity.DifferentialGraded.shiftModule t M)
    (f : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (shiftModule s M) N).X (s - t))
    (hf : HEq f (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D s t (unitElement R M).val
      (by omega : s + 0 - t = s - t)))
    {q k : ℤ} (g : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D N P).X q) (hk : (s - t) + q = k)
    (hzero : _root_.SerrePositivity.DifferentialGraded.compose R (x := shiftModule s M) (y := N) (z := P) g f hk = 0) : g = 0 := by
  cases hN
  cases eq_of_heq hf
  exact dgBarRetractShiftUnit_precompose_zero R D M P g hk hzero

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
