module
public import SerrePositivity.DifferentialGraded.Tensor.Cone
public import SerrePositivity.DifferentialGraded.Tensor.LeftColimits
public import SerrePositivity.DifferentialGraded.Module.LeftQuasiIso
public import SerrePositivity.DifferentialGraded.Module.Acyclic

/-! # 相対K-flat性による左加群変数の準同型保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左右同値と符号付き交換を通じた、opposite上でのacyclic試験。 -/
lemma moduleRelativeKFlat_opposite_test (M : RightModule A D)
    (hM : moduleRelativeKFlat A D M) (C : ModuleCategory A Dᵒᵖ)
    (hC : moduleAcyclic A Dᵒᵖ C) :
    ((BalancedTensor.rightTensorFunctor A Dᵒᵖ M.toFunctor).obj C).Acyclic := by
  let E := leftRightOppositeEquivalence A D
  let L := E.inverse.obj C
  let e : E.functor.obj L ≅ C := E.counitIso.app C
  have hL : leftModuleAcyclic A D (ForgetEnrichment.to (Complex A) L) := by
    intro x n
    exact (hC (op x) n).of_iso ((moduleEvaluation A Dᵒᵖ (op x)).mapIso e.symm)
  exact cochainAcyclic_of_iso (hM (ForgetEnrichment.to (Complex A) L) hL)
    (BalancedTensor.swapIso A D M (ForgetEnrichment.to (Complex A) L) ≪≫
      (BalancedTensor.rightTensorFunctor A Dᵒᵖ M.toFunctor).mapIso e)

/-- 相対K-flat右加群とのtensorは左加群の指定準同型を保存する。 -/
lemma moduleRelativeKFlat_preserves_leftQuasiIso (M : RightModule A D)
    (hM : moduleRelativeKFlat A D M) {L L' : LeftModuleCategory A D} (g : L ⟶ L')
    (hg : leftModuleQuasiIso A D g) :
    QuasiIso ((BalancedTensor.leftTensorFunctor A D M).map g) := by
  let G : LeftModuleCategory A D ⥤ ModuleCategory A Dᵒᵖ := leftModuleToRightOpposite A D
  let T : ModuleCategory A Dᵒᵖ ⥤ Complex A := BalancedTensor.rightTensorFunctor A Dᵒᵖ M.toFunctor
  have hc : moduleAcyclic A Dᵒᵖ (moduleCone A Dᵒᵖ (G.map g)) :=
    (moduleQuasiIso_iff_acyclic_cone A Dᵒᵖ (G.map g)).1 hg
  have ht : (T.obj (moduleCone A Dᵒᵖ (G.map g))).Acyclic :=
    moduleRelativeKFlat_opposite_test A D M hM _ hc
  have hq : QuasiIso (T.map (G.map g)) :=
    (complex_quasiIso_iff_acyclic_cone A _).2
      (cochainAcyclic_of_iso ht (BalancedTensor.rightTensorConeIso A Dᵒᵖ M.toFunctor
        (G.map g)).symm)
  let e : BalancedTensor.leftTensorFunctor A D M ≅ G ⋙ T := BalancedTensor.leftTensorSwapIso A D M
  have he : e.hom.app L ≫ T.map (G.map g) ≫ e.inv.app L' =
      (BalancedTensor.leftTensorFunctor A D M).map g := NatIso.naturality_2 e g
  rw [← he]
  infer_instance

end SerrePositivity.DifferentialGraded
