module
public import SerrePositivity.DifferentialGraded.Module.FreeSphereShift
public import SerrePositivity.DifferentialGraded.Module.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # shiftされた自由sphereの余積

shiftの余積保存はMathlibの同値関手の一般論から再利用する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type w} [Small.{u} J]

/-- 主加群圏の整数shiftとu-small余積の比較。 -/
def moduleShiftCoproductIso (M : J → ModuleCategory A D) (s : ℤ) :
    (∐ M)⟦s⟧ ≅ ∐ (fun t => (M t)⟦s⟧) :=
  PreservesCoproduct.iso (CategoryTheory.shiftFunctor (ModuleCategory A D) s) M

/-- shiftされた自由sphereの余積も自由sphereの余積。 -/
def freeSphereCoproductShiftIso (x : J → D) (n : J → ℤ) (s : ℤ) :
    (∐ fun t => freeSphere A D (x t) (n t))⟦s⟧ ≅
      ∐ fun t => freeSphere A D (x t) (n t - s) :=
  moduleShiftCoproductIso A D (fun t => freeSphere A D (x t) (n t)) s ≪≫
    Limits.Sigma.mapIso (fun t => freeSphereShiftIso A D (x t) (n t) s)

end SerrePositivity.DifferentialGraded
