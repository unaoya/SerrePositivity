module
public import SerrePositivity.HomologicalAlgebra.ChainLinearYonedaZero
public import SerrePositivity.HomologicalAlgebra.ProjectiveExtNaturality
public import Mathlib.Algebra.Homology.SingleHomology

/-! # Actual Mathlib Ext in degree zero and quotient-Hom computations -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
variable {R : Type u} [CommRing R]

/-- A specified projective resolution identifies H0 with its augmentation target. -/
def projectiveResolutionCanonicalH0Iso {X : ModuleCat.{u} R} (P : ProjectiveResolution X) :
    P.complex.homology 0 ≅ X :=
  isoOfQuasiIsoAt P.π 0 ≪≫ singleObjHomologySelfIso (.down ℕ) 0 X

/-- The actual Mathlib Ext0 functor is the represented Hom functor, naturally in coefficients. -/
def projectiveResolutionExtZeroNatIso {X : ModuleCat.{u} R} (P : ProjectiveResolution X) :
    (Ext R (ModuleCat.{u} R) 0).obj (op X) ≅
      (linearCoyoneda R (ModuleCat.{u} R)).obj (op X) :=
  projectiveResolutionExtNatIso P 0 ≪≫ chainLinearYonedaZeroHomologyNatIso P.complex ≪≫
    ((linearCoyoneda R (ModuleCat.{u} R)).mapIso (projectiveResolutionCanonicalH0Iso P).op).symm

/-- The canonical H0 normalization respects the standard lift between resolutions. -/
lemma projectiveResolutionCanonicalH0Iso_lift_naturality
    {X Y : ModuleCat.{u} R} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y) :
    homologyMap (ProjectiveResolution.lift f P Q) 0 ≫ (projectiveResolutionCanonicalH0Iso Q).hom =
      (projectiveResolutionCanonicalH0Iso P).hom ≫ f := by
  change homologyMap (ProjectiveResolution.lift f P Q) 0 ≫
      (homologyMap Q.π 0 ≫ (singleObjHomologySelfIso (.down ℕ) 0 Y).hom) =
    (homologyMap P.π 0 ≫ (singleObjHomologySelfIso (.down ℕ) 0 X).hom) ≫ f
  rw [← Category.assoc, ← homologyMap_comp, ProjectiveResolution.lift_commutes,
    homologyMap_comp, Category.assoc, singleObjHomologySelfIso_hom_naturality,
    ← Category.assoc]

/-- The Ext0 comparison respects the actual first-variable maps as natural coefficient maps. -/
lemma projectiveResolutionExtZeroNatIso_first_naturality
    {X Y : ModuleCat.{u} R} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y) :
    (Ext R (ModuleCat.{u} R) 0).map f.op ≫ (projectiveResolutionExtZeroNatIso P).hom =
      (projectiveResolutionExtZeroNatIso Q).hom ≫
        (linearCoyoneda R (ModuleCat.{u} R)).map f.op := by
  apply NatTrans.ext
  funext J
  let φ := ProjectiveResolution.lift f P Q
  let EP := projectiveResolutionCanonicalH0Iso P
  let EQ := projectiveResolutionCanonicalH0Iso Q
  let F := (linearYoneda R (ModuleCat.{u} R)).obj J
  have hcanon : homologyMap φ 0 ≫ EQ.hom = EP.hom ≫ f :=
    projectiveResolutionCanonicalH0Iso_lift_naturality f P Q
  have hinv : EP.inv ≫ homologyMap φ 0 = f ≫ EQ.inv := by
    apply (cancel_mono EQ.hom).mp
    simp only [Category.assoc, hcanon, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have hExt := projectiveResolutionIsoExt_first_naturality f P Q φ
    (ProjectiveResolution.lift_commutes_zero f P Q) J 0
  change ((Ext R (ModuleCat.{u} R) 0).map f.op).app J ≫
      ((P.isoExt 0 J).hom ≫ (chainLinearYonedaZeroHomologyIso P.complex J).hom ≫ F.map EP.inv.op) =
    ((Q.isoExt 0 J).hom ≫ (chainLinearYonedaZeroHomologyIso Q.complex J).hom ≫ F.map EQ.inv.op) ≫
      F.map f.op
  rw [← Category.assoc, hExt]
  simp only [Category.assoc]
  rw [← Category.assoc (homologyMap ((chainLinearYonedaMap φ).app J) 0),
    chainLinearYonedaZeroHomologyIso_chain_naturality]
  simp only [Category.assoc]
  congr 1
  congr 1
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, hinv]

/-- Actual Mathlib Ext0 and linear Hom agree naturally in both variables. -/
def extZeroLinearCoyonedaNatIso : Ext R (ModuleCat.{u} R) 0 ≅ linearCoyoneda R (ModuleCat.{u} R) :=
  NatIso.ofComponents (fun X => projectiveResolutionExtZeroNatIso (projectiveResolution X.unop))
    (fun f => projectiveResolutionExtZeroNatIso_first_naturality f.unop
      (projectiveResolution _) (projectiveResolution _))

end SerrePositivity
