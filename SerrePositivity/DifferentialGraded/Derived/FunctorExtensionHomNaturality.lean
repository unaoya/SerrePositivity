module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionProjectiveNaturality
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionNaturality

/-! # graph導来延長Hom同値の実際の加群射に対する自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgDerivedExtensionHomEquivOnModules_apply
    (N : ModuleCategory A D) (M : ModuleCategory A E)
    (φ : (dgDerivedExtension A D E F).obj
        ((moduleToDerived A D).obj N) ⟶ (moduleToDerived A E).obj M) :
    dgDerivedExtensionHomEquivOnModules A D E F N M φ =
      (moduleDerivedIso A D
          (moduleCanonicalProjectiveResolution A D N).π
          (moduleCanonicalProjectiveResolution A D N).quasiIso).inv ≫
        dgProjectiveDerivedExtensionHomEquiv A D E F
          (moduleCanonicalProjectiveResolution A D N).obj
          (moduleCanonicalProjectiveResolution A D N).projective M
          ((dgDerivedExtensionResolutionComputation A D E F
            (moduleCanonicalProjectiveResolution A D N)).inv ≫ φ) := by
  simp [dgDerivedExtensionHomEquivOnModules, Iso.homCongr]

lemma dgDerivedExtensionHomEquivOnModules_naturality_right
    (N : ModuleCategory A D) {M M' : ModuleCategory A E}
    (φ : (dgDerivedExtension A D E F).obj
        ((moduleToDerived A D).obj N) ⟶ (moduleToDerived A E).obj M)
    (f : M ⟶ M') :
    dgDerivedExtensionHomEquivOnModules A D E F N M'
        (φ ≫ (moduleToDerived A E).map f) =
      dgDerivedExtensionHomEquivOnModules A D E F N M φ ≫
        (dgDerivedRestriction A D E F).map ((moduleToDerived A E).map f) := by
  rw [dgDerivedExtensionHomEquivOnModules_apply,
    dgDerivedExtensionHomEquivOnModules_apply, ← Category.assoc,
    dgProjectiveDerivedExtensionHomEquiv_naturality_right, Category.assoc]

lemma dgResolutionLift_derived_fac
    {N N' : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D N)
    (Q : ModuleProjectiveResolution A D N') (f : N ⟶ N') :
    (moduleToDerived A D).map (P.lift Q f) ≫
        (moduleToDerived A D).map Q.π =
      (moduleToDerived A D).map P.π ≫
        (moduleToDerived A D).map f := by
  have h := P.lift_fac Q f
  rw [← Functor.map_comp, ← Functor.map_comp] at h
  have h' := moduleQuasiIso_equalizes_boundary A D
    (moduleToDerived A D)
    (moduleToDerived_inverts A D) _ _
    ((toHomotopy_map_eq_iff A (RightModule A D) _ _).mp h)
  simpa only [Functor.map_comp] using h'

lemma dgResolutionLift_derived_inv_naturality
    {N N' : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D N)
    (Q : ModuleProjectiveResolution A D N') (f : N ⟶ N') :
    (moduleDerivedIso A D P.π P.quasiIso).inv ≫
        (moduleToDerived A D).map (P.lift Q f) =
      (moduleToDerived A D).map f ≫
        (moduleDerivedIso A D Q.π Q.quasiIso).inv := by
  apply (cancel_mono (moduleDerivedIso A D Q.π Q.quasiIso).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (moduleDerivedIso A D P.π P.quasiIso).inv ≫
    (moduleToDerived A D).map (P.lift Q f) ≫
      (moduleToDerived A D).map Q.π = _
  rw [dgResolutionLift_derived_fac]
  exact Iso.inv_hom_id_assoc _ _

lemma dgDerivedExtensionHomEquivOnModules_naturality_left
    {N N' : ModuleCategory A D} (M : ModuleCategory A E)
    (f : N ⟶ N')
    (φ : (dgDerivedExtension A D E F).obj
        ((moduleToDerived A D).obj N') ⟶ (moduleToDerived A E).obj M) :
    dgDerivedExtensionHomEquivOnModules A D E F N M
        ((dgDerivedExtension A D E F).map
          ((moduleToDerived A D).map f) ≫ φ) =
      (moduleToDerived A D).map f ≫
        dgDerivedExtensionHomEquivOnModules A D E F N' M φ := by
  rw [dgDerivedExtensionHomEquivOnModules_apply,
    dgDerivedExtensionHomEquivOnModules_apply, ← Category.assoc,
    dgDerivedExtensionResolutionComputation_inv_naturality, Category.assoc,
    dgProjectiveDerivedExtensionHomEquiv_naturality_left, ← Category.assoc,
    dgResolutionLift_derived_inv_naturality, Category.assoc]

end SerrePositivity.DifferentialGraded
