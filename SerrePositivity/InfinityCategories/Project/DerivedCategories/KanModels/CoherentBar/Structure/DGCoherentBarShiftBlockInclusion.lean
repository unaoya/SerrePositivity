module
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut

/-!
概要：シフト間ブロックを元のシフト包含に合成すると、始域のシフト対が消える。
方針：全次数の結合則と実 shift の包含・射影の逆則を適用する。
規約：斉次射の次数は任意で、閉性を要求しない。
使われ方：bar の θ 作用と、末端に bar を加えた HA 右辺との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open DifferentialGraded

private lemma fourfold_cancel_in {A : Type u} [CommRing A] {C : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A C]
    {M S N T : C} {a b q c k : ℤ}
    (i : GradedHom A M S a) (o : GradedHom A S M b)
    (f : GradedHom A M N q) (h : GradedHom A N T c)
    (hab : a + b = 0) (hk : b + q + c = k)
    (hcancel : compose A o i hab = (unitElement A M).val) :
    compose A (compose A h (compose A f o rfl) hk) i (by omega) =
      compose A h f rfl := by
  calc
    _ = compose A h (compose A (compose A f o rfl) i (by omega)) rfl :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum i (compose A f o rfl) h (by omega) hk rfl).symm
    _ = compose A h (compose A f (compose A o i hab) (zero_add q)) rfl := by
      congr 1
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum i o f hab rfl (zero_add q)).symm
    _ = compose A h f rfl := by rw [hcancel, compose_unit]

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgModuleShiftBlock_comp_shiftIn (s t : ℤ) {M N : _root_.SerrePositivity.DifferentialGraded.RightModule R D} {q k : ℤ}
    (f : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D M N).X q) (hk : s + q - t = k) :
    _root_.SerrePositivity.DifferentialGraded.compose R (x := M) (y := shiftModule s M) (z := shiftModule t N)
      (moduleHomShiftBlock R D s t f hk) (moduleShiftInElement R D s M)
        (show -s + k = q + -t by omega) =
      _root_.SerrePositivity.DifferentialGraded.compose R (x := M) (y := N) (z := shiftModule t N)
        (moduleShiftInElement R D t N) f rfl := by
  unfold _root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock
  exact fourfold_cancel_in (A := R) (C := RightModule R D)
    (M := M) (S := shiftModule s M) (N := N) (T := shiftModule t N)
    (a := -s) (b := s) (q := q) (c := -t) (k := k)
    (moduleShiftInElement R D s M) (moduleShiftOutElement R D s M)
    f (moduleShiftInElement R D t N) (neg_add_cancel s) (by omega)
    (moduleShiftInOut R D s M)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
