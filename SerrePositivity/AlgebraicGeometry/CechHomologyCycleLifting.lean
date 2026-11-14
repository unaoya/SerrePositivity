module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
概要：加群の短複体の H の全射性・単射性から、サイクルの持ち上げ・境界の反映を得る。
方針：homologyπ の全射性と homologyι の単射性、および opcycles の具体的な判定。
規約：基底環と加群の宇宙は独立とし、整数係数も大きい宇宙で扱う。
使われ方：F8 の明示的な全複体の完全性を F6・F7 の H の情報から証明する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]
variable (S T : ShortComplex (ModuleCat.{u} R)) (φ : S ⟶ T)

private theorem homologyCycleValue (x : S.cycles) :
    S.homologyι.hom (S.homologyπ.hom x) = S.pOpcycles.hom (S.iCycles.hom x) := by
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
    congrArg (fun f ↦ f.hom x) S.homology_π_ι

private theorem homologyMapCycleValue (x : S.cycles) :
    T.homologyι.hom ((ShortComplex.homologyMap φ).hom (S.homologyπ.hom x)) =
      T.pOpcycles.hom (φ.τ₂.hom (S.iCycles.hom x)) := by
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
    congrArg (fun f ↦ f.hom x) (ShortComplex.π_homologyMap_ι φ)

/-- H の全射性から、目標のサイクルを境界を除いて持ち上げる。 -/
theorem cechCycles_lift_of_homology_surjective
    (h : Function.Surjective (ShortComplex.homologyMap φ).hom)
    (y : T.X₂) (hy : T.g.hom y = 0) :
    ∃ (x : S.X₂) (b : T.X₁), S.g.hom x = 0 ∧ φ.τ₂.hom x = y + T.f.hom b := by
  obtain ⟨a, ha⟩ := h (T.homologyπ.hom (T.cyclesMk y hy))
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance a
  have hx : S.g.hom (S.iCycles.hom z) = 0 := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using congrArg (fun f ↦ f.hom z) S.iCycles_g
  have he := congrArg T.homologyι.hom ha
  rw [homologyMapCycleValue, homologyCycleValue] at he
  have hv : T.iCycles.hom (T.cyclesMk y hy) = y := T.i_cyclesMk y hy
  have he' := he.trans (congrArg (fun x ↦ T.pOpcycles.hom x) hv)
  obtain ⟨b, hb⟩ := (T.moduleCat_pOpcycles_eq_iff _ _).mp he'
  refine ⟨S.iCycles.hom z, b, hx, ?_⟩
  exact ((sub_eq_iff_eq_add).mp hb.symm).trans (add_comm _ _)

/-- H の単射性から、境界へ移るサイクルを元の境界へ戻す。 -/
theorem cechCycles_boundary_of_homology_injective
    (h : Function.Injective (ShortComplex.homologyMap φ).hom)
    (x : S.X₂) (hx : S.g.hom x = 0)
    (hb : ∃ b : T.X₁, T.f.hom b = φ.τ₂.hom x) :
    ∃ a : S.X₁, S.f.hom a = x := by
  let z := S.cyclesMk x hx
  have hv : S.iCycles.hom z = x := S.i_cyclesMk x hx
  have hp : T.pOpcycles.hom (φ.τ₂.hom x) = 0 :=
    (T.moduleCat_pOpcycles_eq_zero_iff _).mpr hb
  have hmap : (ShortComplex.homologyMap φ).hom (S.homologyπ.hom z) = 0 := by
    apply (ModuleCat.mono_iff_injective T.homologyι).mp inferInstance
    rw [homologyMapCycleValue, hv, hp, map_zero]
  have hz : S.homologyπ.hom z = 0 := h (hmap.trans (map_zero _).symm)
  have hs : S.pOpcycles.hom x = 0 := by
    rw [← hv, ← homologyCycleValue, hz, map_zero]
  exact (S.moduleCat_pOpcycles_eq_zero_iff _).mp hs

end SerrePositivity.AlgebraicGeometry
