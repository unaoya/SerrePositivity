module
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra
/-!
概要：シフトブロックを対象・シフト・次数の等式に沿って比較する。
方針：全ての型の等号を明示して消去し、元の Hom の異種等号へ戻す。
規約：閉零射に限らず、全斉次係数とその端点輸送を扱う。
使われ方：prefix の前後で退化を合成した二つの係数を同じブロックへ照合する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgBarRetractShiftBlock_heq
    (M N M' N' : _root_.SerrePositivity.DifferentialGraded.RightModule R D) (hM : M = M') (hN : N = N')
    (s t s' t' : ℤ) (hs : s = s') (ht : t = t')
    {p p' q q' : ℤ} (hp : p = p') (hq : q = q')
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R M N p) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R M' N' p') (hfg : HEq f g)
    (hf : s + p - t = q) (hg : s' + p' - t' = q') :
    HEq (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D s t f hf) (_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock R D s' t' g hg) := by
  cases hM
  cases hN
  cases hs
  cases ht
  cases hp
  cases hq
  cases eq_of_heq hfg
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
