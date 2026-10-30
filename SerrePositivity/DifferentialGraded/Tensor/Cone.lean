module
public import SerrePositivity.DifferentialGraded.Functor.ModuleConeIso
public import SerrePositivity.DifferentialGraded.Tensor.Homotopy
public import SerrePositivity.DifferentialGraded.Tensor.KFlat
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES

/-! # balanced tensorによる標準cone保存と相対K-flatのcone閉性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def rightTensorConeIso (L : LeftModule A D) {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone ((rightTensorFunctor A D L).map f) ≅
      (rightTensorFunctor A D L).obj (moduleCone A D f) := by
  have h : ((rightTensorDG A D L).toComplexFunctor A).map f =
      (rightTensorFunctor A D L).map f := rightTensorDG_map A D L f
  exact eqToIso (congrArg
    (fun g : (rightTensorFunctor A D L).obj M ⟶ (rightTensorFunctor A D L).obj N => mappingCone g)
    h.symm) ≪≫ DGFunctor.moduleConeImageIso A D (rightTensorDG A D L) f

end BalancedTensor

open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 相対K-flat加群は任意の標準coneで閉じる。 -/
lemma moduleRelativeKFlat_cone {M N : ModuleCategory A D} (f : M ⟶ N)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M))
    (hN : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) N)) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (moduleCone A D f)) := by
  intro L hL
  exact cochainAcyclic_of_iso
    (cochainAcyclic_mappingCone ((BalancedTensor.rightTensorFunctor A D L).map f)
      (hM L hL) (hN L hL)) (BalancedTensor.rightTensorConeIso A D L f)

end SerrePositivity.DifferentialGraded
