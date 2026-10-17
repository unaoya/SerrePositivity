module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedProjectiveHomNaturality
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedTensorNaturality

/-! # 再構成導来Hom同値の実際の加群射に対する自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)
variable (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))

lemma endomorphismDerivedTensorHomEquivOnModules_apply
    (N : ModuleCategory A (EndomorphismObject E)) (M : ModuleCategory A D)
    (φ : (endomorphismDerivedTensor A D E).obj
        ((moduleToDerived A (EndomorphismObject E)).obj N) ⟶ (moduleToDerived A D).obj M) :
    endomorphismDerivedTensorHomEquivOnModules A D E hE N M φ =
      (moduleDerivedIso A (EndomorphismObject E)
          (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N).π
          (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N).quasiIso).inv ≫
        endomorphismProjectiveDerivedHomEquiv A D E hE
          (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N).obj
          (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N).projective M
          ((endomorphismDerivedTensorResolutionComputation A D E
            (moduleCanonicalProjectiveResolution A (EndomorphismObject E) N)).inv ≫ φ) := by
  simp [endomorphismDerivedTensorHomEquivOnModules, Iso.homCongr]

lemma endomorphismDerivedTensorHomEquivOnModules_naturality_right
    (N : ModuleCategory A (EndomorphismObject E)) {M M' : ModuleCategory A D}
    (φ : (endomorphismDerivedTensor A D E).obj
        ((moduleToDerived A (EndomorphismObject E)).obj N) ⟶ (moduleToDerived A D).obj M)
    (f : M ⟶ M') :
    endomorphismDerivedTensorHomEquivOnModules A D E hE N M'
        (φ ≫ (moduleToDerived A D).map f) =
      endomorphismDerivedTensorHomEquivOnModules A D E hE N M φ ≫
        (endomorphismDerivedHom A D E hE).map ((moduleToDerived A D).map f) := by
  rw [endomorphismDerivedTensorHomEquivOnModules_apply,
    endomorphismDerivedTensorHomEquivOnModules_apply, ← Category.assoc,
    endomorphismProjectiveDerivedHomEquiv_naturality_right, Category.assoc]

lemma endomorphismResolutionLift_derived_fac
    {N N' : ModuleCategory A (EndomorphismObject E)}
    (P : ModuleProjectiveResolution A (EndomorphismObject E) N)
    (Q : ModuleProjectiveResolution A (EndomorphismObject E) N') (f : N ⟶ N') :
    (moduleToDerived A (EndomorphismObject E)).map (P.lift Q f) ≫
        (moduleToDerived A (EndomorphismObject E)).map Q.π =
      (moduleToDerived A (EndomorphismObject E)).map P.π ≫
        (moduleToDerived A (EndomorphismObject E)).map f := by
  have h := P.lift_fac Q f
  rw [← Functor.map_comp, ← Functor.map_comp] at h
  have h' := moduleQuasiIso_equalizes_boundary A (EndomorphismObject E)
    (moduleToDerived A (EndomorphismObject E))
    (moduleToDerived_inverts A (EndomorphismObject E)) _ _
    ((toHomotopy_map_eq_iff A (RightModule A (EndomorphismObject E)) _ _).mp h)
  simpa only [Functor.map_comp] using h'

lemma endomorphismResolutionLift_derived_inv_naturality
    {N N' : ModuleCategory A (EndomorphismObject E)}
    (P : ModuleProjectiveResolution A (EndomorphismObject E) N)
    (Q : ModuleProjectiveResolution A (EndomorphismObject E) N') (f : N ⟶ N') :
    (moduleDerivedIso A (EndomorphismObject E) P.π P.quasiIso).inv ≫
        (moduleToDerived A (EndomorphismObject E)).map (P.lift Q f) =
      (moduleToDerived A (EndomorphismObject E)).map f ≫
        (moduleDerivedIso A (EndomorphismObject E) Q.π Q.quasiIso).inv := by
  apply (cancel_mono (moduleDerivedIso A (EndomorphismObject E) Q.π Q.quasiIso).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (moduleDerivedIso A (EndomorphismObject E) P.π P.quasiIso).inv ≫
    (moduleToDerived A (EndomorphismObject E)).map (P.lift Q f) ≫
      (moduleToDerived A (EndomorphismObject E)).map Q.π = _
  rw [endomorphismResolutionLift_derived_fac]
  exact Iso.inv_hom_id_assoc _ _

lemma endomorphismDerivedTensorHomEquivOnModules_naturality_left
    {N N' : ModuleCategory A (EndomorphismObject E)} (M : ModuleCategory A D)
    (f : N ⟶ N')
    (φ : (endomorphismDerivedTensor A D E).obj
        ((moduleToDerived A (EndomorphismObject E)).obj N') ⟶ (moduleToDerived A D).obj M) :
    endomorphismDerivedTensorHomEquivOnModules A D E hE N M
        ((endomorphismDerivedTensor A D E).map
          ((moduleToDerived A (EndomorphismObject E)).map f) ≫ φ) =
      (moduleToDerived A (EndomorphismObject E)).map f ≫
        endomorphismDerivedTensorHomEquivOnModules A D E hE N' M φ := by
  rw [endomorphismDerivedTensorHomEquivOnModules_apply,
    endomorphismDerivedTensorHomEquivOnModules_apply, ← Category.assoc,
    endomorphismDerivedTensorResolutionComputation_inv_naturality, Category.assoc,
    endomorphismProjectiveDerivedHomEquiv_naturality_left, ← Category.assoc,
    endomorphismResolutionLift_derived_inv_naturality, Category.assoc]

end SerrePositivity.DifferentialGraded
