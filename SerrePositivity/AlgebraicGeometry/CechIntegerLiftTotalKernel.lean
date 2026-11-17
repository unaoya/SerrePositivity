module

public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
概要：元の同じtotalの関手が核を保つ標準比較。
方針：既存の短完全性とMathlibの有限極限保存の判定を使う。
規約：元のkernelとtotal.mapのkernelの包含を保持する。
使われ方：F8の同じ核のtotalへ元の増大複体から射を持ち上げる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
local notation "up" => ComplexShape.up ℕ

instance cechIntegerLiftTotalFunctor_preservesFiniteLimits : PreservesFiniteLimits
    (cechIntegerLiftTotalFunctor : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up ⥤
      CochainComplex (ModuleCat.{u} ℤ) ℕ) :=
  (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mpr (by
    intro S hS
    have h := cechIntegerLiftTotalFunctor_shortExact S hS
    exact ⟨h.exact, h.mono_f⟩)

variable {K L : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up} (f : K ⟶ L)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ核のtotalと、元のtotalの射の核の標準同型。 -/
def cechIntegerLiftTotalKernelIso :
    HomologicalComplex₂.total (C := ModuleCat.{u} ℤ) (kernel f) up ≅
      kernel (HomologicalComplex₂.total.map f up) := by
  let e := PreservesKernel.iso (cechIntegerLiftTotalFunctor :
    HomologicalComplex₂ (ModuleCat.{u} ℤ) up up ⥤ CochainComplex (ModuleCat.{u} ℤ) ℕ) f
  exact e

set_option backward.isDefEq.respectTransparency false in
/-- 同じ標準比較は、元のkernelの包含のtotalを保持する。 -/
theorem cechIntegerLiftTotalKernelIso_hom_ι :
    (cechIntegerLiftTotalKernelIso f).hom ≫ kernel.ι (HomologicalComplex₂.total.map f up) =
      HomologicalComplex₂.total.map (kernel.ι f) up := by
  let F : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up ⥤ CochainComplex (ModuleCat.{u} ℤ) ℕ :=
    cechIntegerLiftTotalFunctor
  have h := kernelComparison_comp_ι f F
  have he := PreservesKernel.iso_hom F f
  exact (congrArg (fun z ↦ z ≫ kernel.ι (F.map f)) he).trans h

end SerrePositivity.AlgebraicGeometry
