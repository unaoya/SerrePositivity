module
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomHEqAlgebra
/-!
概要：加群 Hom の標的の等号に沿う全次数輸送を、元の係数との異種等号とまとめる。
方針：既存の gradedHomTransportWithHEq を、元の加群 Hom 型へ明示して適用する。
規約：元の加群・次数・等号を保持し、Small は係数 dg 圏だけに要求する。
使われ方：bar の面係数の端点 cast を再計算せず、微分を照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

def dgModuleHomTargetTransport (M N N' : _root_.SerrePositivity.DifferentialGraded.RightModule R D) (h : N = N') (q : ℤ)
    (f : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D M N).X q) :
    {g : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D M N').X q // HEq g f} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := R) (D := _root_.SerrePositivity.DifferentialGraded.RightModule R D)
    (x := M) (y := N) (x' := M) (y' := N') rfl h rfl f

lemma dgModuleHomTargetTransport_d (M N N' : _root_.SerrePositivity.DifferentialGraded.RightModule R D) (h : N = N') (q r : ℤ)
    (f : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D M N).X q) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D M N').d q r (dgModuleHomTargetTransport R D M N N' h q f).val =
      (dgModuleHomTargetTransport R D M N N' h r ((moduleHom R D M N).d q r f)).val := by
  cases h
  rfl

lemma dgModuleHomTargetTransport_zero (M N N' : _root_.SerrePositivity.DifferentialGraded.RightModule R D) (h : N = N') (q : ℤ) :
    (dgModuleHomTargetTransport R D M N N' h q 0).val = 0 := by
  cases h
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
