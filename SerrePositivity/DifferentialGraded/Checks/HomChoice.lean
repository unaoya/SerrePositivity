module
public import SerrePositivity.DifferentialGraded.Derived.Projective

/-! # U10b7d：解像度を替えた導来Homの自然同型と整合性 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

example {M : ModuleCategory A D} (P Q : ModuleProjectiveResolution A D M) :
    Q.derivedHom ≅ P.derivedHom := P.derivedHomIso Q

example {M : ModuleCategory A D} (P Q : ModuleProjectiveResolution A D M)
    (s : P.obj ⟶ Q.obj)
    (hs : (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map Q.π =
      (moduleToHomotopy A D).map P.π) :
    (P.derivedHomIso Q).hom = moduleDerivedHomOutPrecomp A D P.projective Q.projective s :=
  P.derivedHomIso_hom_eq Q s hs

example {M : ModuleCategory A D} (P Q R : ModuleProjectiveResolution A D M) :
    Q.derivedHomIso R ≪≫ P.derivedHomIso Q = P.derivedHomIso R := P.derivedHomIso_trans Q R

example {M : ModuleCategory A D} (P : ModuleProjectiveResolution A D M) :
    moduleResolvedHomOut A D M ≅ P.derivedHom :=
  P.derivedHomIso (moduleCanonicalProjectiveResolution A D M)

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded
#print axioms ModuleProjectiveResolution.mk
#print axioms moduleCanonicalProjectiveResolution
#print axioms ModuleProjectiveResolution.comparison
#print axioms ModuleProjectiveResolution.comparison_quasiIso
#print axioms ModuleProjectiveResolution.comparison_fac
#print axioms ModuleProjectiveResolution.comparison_isIso_homotopy
#print axioms ModuleProjectiveResolution.comparison_unique
#print axioms ModuleProjectiveResolution.comparison_comp
#print axioms ModuleProjectiveResolution.comparison_self
#print axioms ModuleProjectiveResolution.derivedHom
#print axioms ModuleProjectiveResolution.derivedHomComputation
#print axioms ModuleProjectiveResolution.derivedHomIso
#print axioms ModuleProjectiveResolution.derivedHomIso_app
#print axioms ModuleProjectiveResolution.derivedHomIso_hom_eq
#print axioms ModuleProjectiveResolution.derivedHomIso_self
#print axioms ModuleProjectiveResolution.derivedHomIso_trans
#print axioms moduleCanonicalProjectiveResolution_derivedHom
