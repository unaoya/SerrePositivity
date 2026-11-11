module
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut
/-!
概要：始域の整数シフトを解いた全次数 Hom の線形座標を与える。
方針：元の shift 包含・射影の両逆則を斉次合成に使う。
規約：全次数と符号を保持し、閉零射やホモトピー類に制限しない。
使われ方：正規化 Hom の列を native 余錐の次数付き成分と比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgCoherentBarHom_compose_smul_left {M N P : _root_.SerrePositivity.DifferentialGraded.RightModule R D} {p q k : ℤ}
    (r : R) (g : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D N P).X q) (f : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D M N).X p)
    (hk : p + q = k) :
    _root_.SerrePositivity.DifferentialGraded.compose R (x := M) (y := N) (z := P) (r • g) f hk =
      r • _root_.SerrePositivity.DifferentialGraded.compose R (x := M) (y := N) (z := P) g f hk := by
  simp only [_root_.SerrePositivity.DifferentialGraded.compose, _root_.SerrePositivity.DifferentialGraded.forward, TensorProduct.tmul_smul, map_smul]
  exact smul_comm _ _ _

def dgCoherentBarShiftedHomEquiv (s q : ℤ) (M N : _root_.SerrePositivity.DifferentialGraded.RightModule R D) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (shiftModule s M) N).X q ≃ₗ[R]
      (_root_.SerrePositivity.DifferentialGraded.moduleHom R D M N).X (q - s) where
  toFun z := compose R (x := M) (y := shiftModule s M) (z := N) z
    (moduleShiftInElement R D s M) (by omega)
  invFun z := compose R (x := shiftModule s M) (y := M) (z := N) z
    (moduleShiftOutElement R D s M) (by omega)
  left_inv z := by
    calc
      _ = compose R (x := shiftModule s M) (y := shiftModule s M) (z := N) z
          (compose R (x := shiftModule s M) (y := M) (z := shiftModule s M)
            (moduleShiftInElement R D s M) (moduleShiftOutElement R D s M)
            (add_neg_cancel s)) (zero_add q) :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum
          (w := shiftModule s M) (x := M) (y := shiftModule s M) (z := N)
          (p := s) (q := -s) (r := q) (a := 0) (b := q - s) (t := q)
          (moduleShiftOutElement R D s M) (moduleShiftInElement R D s M) z
          (add_neg_cancel s) (by omega) (zero_add q)).symm
      _ = z := by rw [moduleShiftOutIn, compose_unit]
  right_inv z := by
    calc
      _ = compose R (x := M) (y := M) (z := N) z
          (compose R (x := M) (y := shiftModule s M) (z := M)
            (moduleShiftOutElement R D s M) (moduleShiftInElement R D s M)
            (neg_add_cancel s)) (zero_add (q - s)) :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum
          (w := M) (x := shiftModule s M) (y := M) (z := N)
          (p := -s) (q := s) (r := q - s) (a := 0) (b := q) (t := q - s)
          (moduleShiftInElement R D s M) (moduleShiftOutElement R D s M) z
          (neg_add_cancel s) (by omega)
          (zero_add (q - s))).symm
      _ = z := by rw [moduleShiftInOut, compose_unit]
  map_add' z w := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_left _ _ _ _
  map_smul' r z := dgCoherentBarHom_compose_smul_left R D r z _ _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
