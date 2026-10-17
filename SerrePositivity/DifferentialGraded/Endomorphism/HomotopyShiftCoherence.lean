module
public import SerrePositivity.DifferentialGraded.Endomorphism.ShiftAddCoherence
public import SerrePositivity.DifferentialGraded.Module.ShiftHomotopy

/-! # 正規化shift比較を主ホモトピー圏へ降ろす -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (B : Type w) [DGCategory A B] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

/-- 全Hom写像から得た整合的shift比較を境界商へ降ろす。 -/
@[instance_reducible]
def dgModuleFunctorHomotopyCommShift : F.onHomotopy.CommShift ℤ := by
  letI := dgModuleFunctorCommShift A D B F
  unfold DGFunctor.onHomotopy
  infer_instance

/-- 閉零加群から主Kへの因子分解の自然同型。 -/
def dgModuleFunctorHomotopyFacIso :
    moduleToHomotopy A D ⋙ F.onHomotopy ≅ F.onClosed ⋙ moduleToHomotopy A B :=
  Quotient.lift.isLift _ _ _

section
local instance : F.onClosed.CommShift ℤ := dgModuleFunctorCommShift A D B F
local instance : F.onHomotopy.CommShift ℤ := dgModuleFunctorHomotopyCommShift A D B F

lemma dgModuleFunctorHomotopyFacIso_commShift :
    NatTrans.CommShift (dgModuleFunctorHomotopyFacIso A D B F).hom ℤ := by
  unfold dgModuleFunctorHomotopyFacIso
  exact Quotient.liftCommShift_compatibility _ _ _ _

end
end SerrePositivity.DifferentialGraded
