module
public import SerrePositivity.DifferentialGraded.Module.MaurerCartanTriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberObject
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # K(D) の三角的対象条件を全 dg 加群へ戻す

概要：同型で閉じた三角的対象条件は実零加群、整数シフト、cone、shifted cone で閉じる。
方針：標準 cone 三角形と商関手の shift 比較を使う。
規約：周囲の ∞ 安定性は独立に証明済み。使われ方：表現可能加群の同値閉包の制限。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- K(D) の対象条件を実 dg 加群の対象へ戻す。 -/
def dgModuleHomotopyProperty (P : ObjectProperty (ModuleHomotopyCategory A D))
    (M : RightModule A D) : Prop :=
  P ((moduleToHomotopy A D).obj (ForgetEnrichment.of (Complex A) M))

variable (P : ObjectProperty (ModuleHomotopyCategory A D))
variable [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

/-- 三角的対象条件は実零加群を含む。 -/
lemma dgModuleHomotopyProperty_zero :
    dgModuleHomotopyProperty A D P (zeroModule A D) :=
  P.prop_of_isZero ((moduleToHomotopy A D).map_isZero (moduleZero_isZero A D))

/-- 三角的対象条件は実加群の全整数シフトで閉じる。 -/
lemma dgModuleHomotopyProperty_shift (M : ModuleCategory A D) (s : ℤ)
    (hM : dgModuleHomotopyProperty A D P (ForgetEnrichment.to (Complex A) M)) :
    dgModuleHomotopyProperty A D P (shiftModule s (ForgetEnrichment.to (Complex A) M)) := by
  change P ((moduleToHomotopy A D).obj (M⟦s⟧))
  exact P.prop_of_iso (((moduleToHomotopy A D).commShiftIso s).app M).symm
    (P.le_shift s _ hM)

/-- 三角的対象条件は閉 dg 加群射の標準 cone で閉じる。 -/
lemma dgModuleHomotopyProperty_cone {M N : ModuleCategory A D} (f : M ⟶ N)
    (hM : dgModuleHomotopyProperty A D P (ForgetEnrichment.to (Complex A) M))
    (hN : dgModuleHomotopyProperty A D P (ForgetEnrichment.to (Complex A) N)) :
    dgModuleHomotopyProperty A D P
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) := by
  exact P.ext_of_isTriangulatedClosed₃ (moduleHomotopyConeTriangle A D f)
    (moduleHomotopyConeTriangle_distinguished A D f) hM hN

/-- 三角的対象条件は実 fiber 対象 cone(f)[−1] で閉じる。 -/
lemma dgModuleHomotopyProperty_fiber {M N : ModuleCategory A D} (f : M ⟶ N)
    (hM : dgModuleHomotopyProperty A D P (ForgetEnrichment.to (Complex A) M))
    (hN : dgModuleHomotopyProperty A D P (ForgetEnrichment.to (Complex A) N)) :
    dgModuleHomotopyProperty A D P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiber A D f) :=
  dgModuleHomotopyProperty_shift A D P (moduleCone A D f) (-1)
    (dgModuleHomotopyProperty_cone A D P f hM hN)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
