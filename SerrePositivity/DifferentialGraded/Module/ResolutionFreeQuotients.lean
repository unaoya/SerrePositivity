module
public import SerrePositivity.DifferentialGraded.Module.ShiftCoproduct
public import SerrePositivity.DifferentialGraded.Module.ResolutionGradedSteps

/-! # 可算cell付加の商は自由sphereの余積

既存の真の商の対象を、shiftを含まない自由sphere族に同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 次数n+1のkernel cycleを消す付加の商は次数nの自由sphere。 -/
def moduleKernelCellQuotientFamily {M N : ModuleCategory A D} (f : M ⟶ N) :
    ModuleKernelCellIndex A D f → ModuleCategory A D :=
  fun t => freeSphere A D t.1 t.2.1

/-- 真の商対象 `(∐ freeSphere(n+1))[1]` の自由sphere余積による表示。 -/
def moduleKernelCellQuotientFreeIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleKernelCellSource A D f)⟦(1 : ℤ)⟧ ≅ ∐ moduleKernelCellQuotientFamily A D f :=
  moduleShiftCoproductIso A D (moduleKernelCellFamily A D f) 1 ≪≫
    Limits.Sigma.mapIso (fun t : ModuleKernelCellIndex A D f =>
      freeSphereShiftIso A D t.1 (t.2.1 + 1) 1 ≪≫
        eqToIso (congrArg (freeSphere A D t.1) (by omega : t.2.1 + 1 - 1 = t.2.1)))

end SerrePositivity.DifferentialGraded
