module
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomologyNaturality
public import Mathlib.CategoryTheory.Types.Basic

/-! # 任意の導来射に自然な代表加群のHom計算

局所化の射宇宙へホモロジーの値をULiftし、局所化の普遍性で自然同型を延長する。
小さいHom宇宙や対象集合への置換は行わない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleRepresentableDerivedCoyoneda (x : D) :
    DerivedModuleCategory A D ⥤ Type (max (u + 1) v) :=
  coyoneda.obj (op ((moduleToDerived A D).obj
    (ForgetEnrichment.of (Complex A) (representable A x))))

def moduleDerivedHomologyLift (x : D) :
    DerivedModuleCategory A D ⥤ Type (max (u + 1) v) :=
  moduleDerivedHomology A D x 0 ⋙ forget (ModuleCat.{u} A) ⋙
    uliftFunctor.{max (u + 1) v, u}

def moduleRepresentableHomologyPreNatIso (x : D) :
    moduleToDerived A D ⋙ moduleRepresentableDerivedCoyoneda A D x ≅
      moduleToDerived A D ⋙ moduleDerivedHomologyLift A D x :=
  NatIso.ofComponents (fun N =>
    ((moduleRepresentableDerivedHomologyEquiv A D x N).trans Equiv.ulift.symm).toIso) (by
      intro M N g
      ext f
      have hg : (moduleDerivedHomology A D x 0).map ((moduleToDerived A D).map g) =
          HomologicalComplex.homologyMap ((moduleEvaluation A D x).map g) 0 := by
        exact eq_of_heq (Functor.hcongr_hom (moduleDerivedHomology_fac A D x 0) g)
      change ULift.up (moduleRepresentableDerivedHomologyEquiv A D x N
        (f ≫ (moduleToDerived A D).map g)) =
        ULift.up ((moduleDerivedHomology A D x 0).map ((moduleToDerived A D).map g)
          (moduleRepresentableDerivedHomologyEquiv A D x M f))
      rw [hg, moduleRepresentableDerivedHomologyEquiv_postcompose]
      rfl)

def moduleRepresentableHomologyNatIso (x : D) :
    moduleRepresentableDerivedCoyoneda A D x ≅ moduleDerivedHomologyLift A D x :=
  Localization.liftNatIso (moduleToDerived A D) (moduleQuasiIso A D)
    (moduleToDerived A D ⋙ moduleRepresentableDerivedCoyoneda A D x)
    (moduleToDerived A D ⋙ moduleDerivedHomologyLift A D x)
    (moduleRepresentableDerivedCoyoneda A D x) (moduleDerivedHomologyLift A D x)
    (moduleRepresentableHomologyPreNatIso A D x)

lemma moduleRepresentableHomologyNatIso_app_obj (x : D) (N : ModuleCategory A D)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      (moduleToDerived A D).obj N) :
    (moduleRepresentableHomologyNatIso A D x).hom.app ((moduleToDerived A D).obj N) f =
      ULift.up (moduleRepresentableDerivedHomologyEquiv A D x N f) := by
  simp only [moduleRepresentableHomologyNatIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, Localization.Lifting.compLeft_iso, Iso.refl_hom]
  rfl

lemma moduleRepresentableHomologyNatIso_app (x : D) (X : DerivedModuleCategory A D)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ X) :
    (moduleRepresentableHomologyNatIso A D x).hom.app X f =
      ULift.up (moduleRepresentableDerivedHomEquiv A D x X f) := by
  obtain ⟨⟨N⟩⟩ := X
  exact moduleRepresentableHomologyNatIso_app_obj A D x N f

lemma moduleRepresentableDerivedHomEquiv_naturality (x : D)
    {X Y : DerivedModuleCategory A D} (g : X ⟶ Y)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ X) :
    moduleRepresentableDerivedHomEquiv A D x Y (f ≫ g) =
      (moduleDerivedHomology A D x 0).map g (moduleRepresentableDerivedHomEquiv A D x X f) := by
  have h := congrArg (fun k => k f) ((moduleRepresentableHomologyNatIso A D x).hom.naturality g)
  change (moduleRepresentableHomologyNatIso A D x).hom.app Y (f ≫ g) =
    ULift.up ((moduleDerivedHomology A D x 0).map g
      ((moduleRepresentableHomologyNatIso A D x).hom.app X f).down) at h
  rw [moduleRepresentableHomologyNatIso_app, moduleRepresentableHomologyNatIso_app] at h
  exact congrArg ULift.down h

lemma moduleRepresentableDerivedHomLinearEquiv_naturality (x : D)
    {X Y : DerivedModuleCategory A D} (g : X ⟶ Y)
    (f : (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ X) :
    moduleRepresentableDerivedHomLinearEquiv A D x Y (f ≫ g) =
      (moduleDerivedHomology A D x 0).map g
        (moduleRepresentableDerivedHomLinearEquiv A D x X f) :=
  moduleRepresentableDerivedHomEquiv_naturality A D x g f

end SerrePositivity.DifferentialGraded
