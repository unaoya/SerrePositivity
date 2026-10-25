module
public import SerrePositivity.InfinityCategories.Derived.DGModuleHomEndpointTransport
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarShiftBlockInclusion
public import SerrePositivity.InfinityCategories.DGNerve.Algebra

/-!
概要：標的を等号で移送した単位シフトブロックと、元のシフト包含の合成を計算する。
方針：端点の等号を消去し、全次数ブロックの shift 対消去と単位則を使う。
規約：次数の等式と元の対象の等号を保持する。
使われ方：bar の面ブロックを、削除単体の実包含へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgModuleUnitShiftBlock_comp_shiftIn_heq (M N : RightModule R D) (h : M = N)
    (s t k : ℤ) (hk : s + 0 - t = k) (ht : -s + k = -t) :
    HEq (compose R (x := M) (y := shiftModule s M) (z := shiftModule t N)
      (dgModuleHomTargetTransport R D (shiftModule s M) (shiftModule t M) (shiftModule t N)
        (congrArg (shiftModule t) h) k
        (moduleHomShiftBlock R D s t (M := M) (N := M) (unitElement R M).val hk)).val
      (moduleShiftInElement R D s M) ht)
      (moduleShiftInElement R D t N) := by
  cases h
  change HEq (compose R (x := M) (y := shiftModule s M) (z := shiftModule t M)
    (moduleHomShiftBlock R D s t (M := M) (N := M) (unitElement R M).val hk)
    (moduleShiftInElement R D s M) ht) (moduleShiftInElement R D t M)
  have hb := dgModuleShiftBlock_comp_shiftIn R D s t (M := M) (N := M) (unitElement R M).val hk
  have hc := gradedHom_compose_heq (A := R) (D := RightModule R D)
    (x := M) (y := shiftModule s M) (z := shiftModule t M)
    (x' := M) (y' := shiftModule s M) (z' := shiftModule t M)
    (p := -s) (q := k) (k := -t) (p' := -s) (q' := k) (k' := 0 + -t)
    rfl rfl rfl rfl rfl (by omega)
    (moduleHomShiftBlock R D s t (M := M) (N := M) (unitElement R M).val hk)
    (moduleShiftInElement R D s M)
    (moduleHomShiftBlock R D s t (M := M) (N := M) (unitElement R M).val hk)
    (moduleShiftInElement R D s M) (HEq.refl _) (HEq.refl _) ht (by omega)
  exact hc.trans ((heq_of_eq hb).trans
    (compose_unit_of_heq (A := R) (D := RightModule R D)
      (moduleShiftInElement R D t M) (unitElement R M).val rfl rfl rfl (HEq.refl _)))

end SerrePositivity.InfinityCategories
