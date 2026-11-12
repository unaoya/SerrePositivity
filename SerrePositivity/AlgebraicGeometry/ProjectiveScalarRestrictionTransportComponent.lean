module

public import SerrePositivity.AlgebraicGeometry.ProjectiveScalarRestrictionTransport

/-!
概要：係数制限した加群との同型で移した作用を、指定した成分上で計算する。
方針：同型の逆で B 加群へ戻し、成分の写像の可換式を使う。
規約：成分の加群自体には B 作用を仮定しない。
使われ方：Rees の Čech 直和比較で、lof の像の斉次作用を同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory

universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable (Y : ModuleCat.{u} B) {A C Z : ModuleCat.{u} R}
variable (e : (ModuleCat.restrictScalars (algebraMap R B)).obj Y ≅ Z)

/-- 比較で移した B 作用は、成分の写像の可換式に沿って成分を移す。 -/
theorem projectiveScalarRestrictionTransportOfIso_component_smul
    (a : A ⟶ (ModuleCat.restrictScalars (algebraMap R B)).obj Y)
    (c : C ⟶ (ModuleCat.restrictScalars (algebraMap R B)).obj Y)
    (l : A ⟶ Z) (k : C ⟶ Z) (s : A ⟶ C) (b : B)
    (hl : a ≫ e.hom = l) (hk : c ≫ e.hom = k)
    (hs : a ≫ (ModuleCat.restrictScalars (algebraMap R B)).map (b • 𝟙 Y) = s ≫ c)
    (x : A) :
    letI := projectiveScalarRestrictionTransportModuleOfIso Y e
    b • l.hom x = k.hom (s.hom x) := by
  letI := projectiveScalarRestrictionTransportModuleOfIso Y e
  let L := projectiveScalarRestrictionTransportLinearEquivOfIso Y e
  have hL (z : A) : L (l.hom z) = (a.hom z : Y) := by
    change e.inv.hom (l.hom z) = a.hom z
    have hz : e.hom.hom (a.hom z) = l.hom z := by
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
        congrArg (fun f : A ⟶ Z ↦ f.hom z) hl
    rw [← hz]
    exact e.toLinearEquiv.symm_apply_apply (a.hom z)
  have hK (z : C) : L (k.hom z) = (c.hom z : Y) := by
    change e.inv.hom (k.hom z) = c.hom z
    have hz : e.hom.hom (c.hom z) = k.hom z := by
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
        congrArg (fun f : C ⟶ Z ↦ f.hom z) hk
    rw [← hz]
    exact e.toLinearEquiv.symm_apply_apply (c.hom z)
  have hsx := congrArg
    (fun f : A ⟶ (ModuleCat.restrictScalars (algebraMap R B)).obj Y ↦ f.hom x) hs
  change b • (a.hom x : Y) = (c.hom (s.hom x) : Y) at hsx
  apply L.injective
  rw [map_smul, hL, hK]
  exact hsx

end SerrePositivity.AlgebraicGeometry
