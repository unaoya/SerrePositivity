module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.ShiftUnitIdentity
public import SerrePositivity.DifferentialGraded.Module.ShiftBlockComposition
public import SerrePositivity.InfinityCategories.DGNerve.NestedCut
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
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgBarRetractShiftUnit_inverse (s t : ℤ) (M : RightModule R D) :
    compose R (x := shiftModule t M) (y := shiftModule s M) (z := shiftModule t M)
      (moduleHomShiftBlock R D s t (unitElement R M).val (by omega : s + 0 - t = s - t))
      (moduleHomShiftBlock R D t s (unitElement R M).val (by omega : t + 0 - s = t - s))
      (by omega : (t - s) + (s - t) = 0) =
      (unitElement R (shiftModule t M)).val := by
  have h := moduleHomShiftBlock_comp R D t s t (unitElement R M).val (unitElement R M).val
    (by omega : t + 0 - s = t - s) (by omega : s + 0 - t = s - t)
    (by omega : (t - s) + (s - t) = 0)
  rw [unit_compose] at h
  exact h.trans (dgBarRetractShiftBlock_unit R D t M)

lemma dgBarRetractShiftUnit_precompose_zero {s t q k : ℤ}
    (M N : RightModule R D) (f : (moduleHom R D (shiftModule t M) N).X q)
    (hk : (s - t) + q = k)
    (hf : compose R (x := shiftModule s M) (y := shiftModule t M) (z := N) f
      (moduleHomShiftBlock R D s t (unitElement R M).val (by omega : s + 0 - t = s - t))
      hk = 0) : f = 0 := by
  have h := compose_assoc_of_sum (A := R) (D := RightModule R D)
    (w := shiftModule t M) (x := shiftModule s M) (y := shiftModule t M) (z := N)
    (p := t - s) (q := s - t) (r := q) (a := 0) (b := k) (t := q)
    (moduleHomShiftBlock R D t s (unitElement R M).val (by omega : t + 0 - s = t - s))
    (moduleHomShiftBlock R D s t (unitElement R M).val (by omega : s + 0 - t = s - t))
    f (by omega) hk (zero_add q)
  rw [dgBarRetractShiftUnit_inverse R D s t M, compose_unit, hf, DGNerve.zero_compose] at h
  exact h

lemma dgBarRetractShiftUnit_transport_precompose_zero (s t : ℤ)
    (M N P : RightModule R D) (hN : N = shiftModule t M)
    (f : (moduleHom R D (shiftModule s M) N).X (s - t))
    (hf : HEq f (moduleHomShiftBlock R D s t (unitElement R M).val
      (by omega : s + 0 - t = s - t)))
    {q k : ℤ} (g : (moduleHom R D N P).X q) (hk : (s - t) + q = k)
    (hzero : compose R (x := shiftModule s M) (y := N) (z := P) g f hk = 0) : g = 0 := by
  cases hN
  cases eq_of_heq hf
  exact dgBarRetractShiftUnit_precompose_zero R D M P g hk hzero

end SerrePositivity.InfinityCategories
