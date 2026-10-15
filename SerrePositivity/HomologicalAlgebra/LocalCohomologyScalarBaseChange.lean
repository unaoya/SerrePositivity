module
public import SerrePositivity.HomologicalAlgebra.GeneralLocalCohomologyBaseChange
public import SerrePositivity.HomologicalAlgebra.LocalCohomologyAction

/-! # Ring change for the actual scalar endomorphisms on local cohomology -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {R S C : Type u} [CommRing R] [CommRing S] [CommRing C]
variable [Algebra R S] [Algebra S C] [Algebra R C] [IsScalarTower R S C]

/-- Identify the restricted coefficient algebra with its given base-ring module,
using the actual algebra tower. -/
def algebraTowerCoefficientRestrictIso :
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S C) ≅ ModuleCat.of R C :=
  (LinearEquiv.toModuleIso
    (X₁ := ModuleCat.of R C)
    (X₂ := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S C))
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change (r • (x : C) : C) = (algebraMap R S r) • (x : C)
        simp only [Algebra.smul_def]
        rw [IsScalarTower.algebraMap_apply R S C r] }).symm

/-- Multiplication by a coefficient algebra element respects the actual module identification. -/
lemma algebraTowerCoefficientRestrictIso_mul (c : C) :
    (ModuleCat.restrictScalars (algebraMap R S)).map
        (ModuleCat.ofHom (LinearMap.mulLeft S c)) ≫
        (algebraTowerCoefficientRestrictIso (R := R) (S := S) (C := C)).hom =
      (algebraTowerCoefficientRestrictIso (R := R) (S := S) (C := C)).hom ≫
        ModuleCat.ofHom (LinearMap.mulLeft R c) := by
  ext x
  rfl

/-- The concrete scalar endomorphisms used in the paper vanish over one
coefficient ring exactly when they vanish over the other, in every degree. -/
lemma localCohomologyScalarEndomorphism_ring_change_eq_zero_iff
    [IsNoetherianRing R] [IsNoetherianRing S] {e : ℕ} (z : Fin e → R) (J : Ideal S)
    (h : ((Ideal.span (Set.range z)).map (algebraMap R S)).radical = J.radical)
    (i : ℕ) (c : C) :
    HomologicalAlgebra.localCohomologyScalarEndomorphism (Ideal.span (Set.range z)) i C c = 0 ↔
      HomologicalAlgebra.localCohomologyScalarEndomorphism J i C c = 0 := by
  let U := ModuleCat.restrictScalars (algebraMap R S)
  let F := localCohomology (Ideal.span (Set.range z)) i
  let E := algebraTowerCoefficientRestrictIso (R := R) (S := S) (C := C)
  let f : ModuleCat.of S C ⟶ ModuleCat.of S C := ModuleCat.ofHom (LinearMap.mulLeft S c)
  let g : ModuleCat.of R C ⟶ ModuleCat.of R C := ModuleCat.ofHom (LinearMap.mulLeft R c)
  have hw : F.map (U.map f) ≫ (F.mapIso E).hom = (F.mapIso E).hom ≫ F.map g := by
    change F.map (U.map f) ≫ F.map E.hom = F.map E.hom ≫ F.map g
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg F.map (algebraTowerCoefficientRestrictIso_mul (R := R) (S := S) c)
  have hzero : F.map (U.map f) = 0 ↔ F.map g = 0 := by
    constructor
    · intro hf
      apply (cancel_epi (F.mapIso E).hom).mp
      simpa only [hf, zero_comp, comp_zero] using hw.symm
    · intro hg
      apply (cancel_mono (F.mapIso E).hom).mp
      simpa only [hg, zero_comp, comp_zero] using hw
  exact hzero.symm.trans
    (localCohomologyRestrictScalarsSupport_map_eq_zero_iff z (algebraMap R S) J h i f)

end SerrePositivity
