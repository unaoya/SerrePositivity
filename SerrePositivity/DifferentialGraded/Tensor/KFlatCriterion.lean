module
public import SerrePositivity.DifferentialGraded.Tensor.QuasiIsoLeft
public import SerrePositivity.DifferentialGraded.Module.LeftZero

/-! # 相対K-flat性と左準同型保存の同値 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
open scoped ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左のacyclic消滅条件は、任意の指定準同型の保存と同値。 -/
lemma moduleRelativeKFlat_iff_preserves_leftQuasiIso (M : RightModule A D) :
    moduleRelativeKFlat A D M ↔
      ∀ {L L' : LeftModuleCategory A D} (g : L ⟶ L'), leftModuleQuasiIso A D g →
        QuasiIso ((BalancedTensor.leftTensorFunctor A D M).map g) := by
  constructor
  · intro h L L' g hg
    exact moduleRelativeKFlat_preserves_leftQuasiIso A D M h g hg
  · intro h L hL
    let N := ForgetEnrichment.of (Complex A) L
    let Z := leftModuleZero A D
    let g : N ⟶ Z := 0
    have hg : leftModuleQuasiIso A D g := by
      apply (leftModuleQuasiIso_iff A D g).2
      intro x
      have hz : ((leftModuleEvaluation A D x).obj Z).Acyclic :=
        acyclic_of_isZero _ (leftModuleZero_evaluation_isZero A D x)
      exact ⟨fun n => (quasiIsoAt_iff_exactAt' _ n (hz n)).2 (hL x n)⟩
    have hq := h g hg
    have hz : ((BalancedTensor.leftTensorFunctor A D M).obj Z).Acyclic :=
      acyclic_of_isZero _ ((BalancedTensor.leftTensorFunctor A D M).map_isZero
        (leftModuleZero_isZero A D))
    intro n
    exact (exactAt_iff_of_quasiIsoAt ((BalancedTensor.leftTensorFunctor A D M).map g) n).2 (hz n)

/-- 零右加群は任意のacyclic左加群とのtensorで消える。 -/
lemma moduleRelativeKFlat_zero : moduleRelativeKFlat A D (zeroModule A D) := by
  intro L _
  exact acyclic_of_isZero _ ((BalancedTensor.rightTensorFunctor A D L).map_isZero
    (moduleZero_isZero A D))

end SerrePositivity.DifferentialGraded
