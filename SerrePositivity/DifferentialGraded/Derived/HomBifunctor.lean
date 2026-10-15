module
public import SerrePositivity.DifferentialGraded.Derived.HomChoice
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveResolutionLift
public import Mathlib.CategoryTheory.Localization.Opposite

/-! # 射影解像度による導来Hom双関手

任意の証明付き解像度族に対して始域の反変関手性を構成し、両変数を指定局所化へ運ぶ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

def moduleResolutionHomSourceFunctor
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    (ModuleCategory A D)ᵒᵖ ⥤ (DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat A)) where
  obj X := (R X.unop).derivedHom
  map {X Y} f := moduleDerivedHomOutPrecomp A D (R Y.unop).projective (R X.unop).projective
    ((R Y.unop).lift (R X.unop) f.unop)
  map_id X := by
    let P := R X.unop
    change moduleDerivedHomOutPrecomp A D P.projective P.projective (P.lift P (𝟙 X.unop)) = 𝟙 _
    calc
      _ = moduleDerivedHomOutPrecomp A D P.projective P.projective (𝟙 P.obj) :=
        moduleDerivedHomOutPrecomp_eq_of_homotopy_map_eq A D P.projective P.projective
          ((P.lift_id).trans ((moduleToHomotopy A D).map_id _).symm)
      _ = _ := moduleDerivedHomOutPrecomp_id A D P.obj P.projective
  map_comp {X Y Z} f g := by
    let P := R Z.unop
    let Q := R Y.unop
    let S := R X.unop
    change moduleDerivedHomOutPrecomp A D P.projective S.projective
      (P.lift S (g.unop ≫ f.unop)) =
        moduleDerivedHomOutPrecomp A D Q.projective S.projective (Q.lift S f.unop) ≫
          moduleDerivedHomOutPrecomp A D P.projective Q.projective (P.lift Q g.unop)
    rw [← moduleDerivedHomOutPrecomp_comp]
    apply moduleDerivedHomOutPrecomp_eq_of_homotopy_map_eq A D P.projective S.projective
    exact (P.lift_comp Q S g.unop f.unop).symm.trans
      ((moduleToHomotopy A D).map_comp _ _).symm

lemma moduleResolutionHomSourceFunctor_inverts
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    (moduleQuasiIso A D).op.IsInvertedBy (moduleResolutionHomSourceFunctor A D R) := by
  intro X Y f hf
  change moduleQuasiIso A D f.unop at hf
  exact moduleDerivedHomOutPrecomp_isIso A D (R Y.unop).projective (R X.unop).projective
    ((R Y.unop).lift (R X.unop) f.unop) ((R Y.unop).lift_quasiIso (R X.unop) f.unop hf)

def moduleResolutionDerivedHomBifunctor
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    (DerivedModuleCategory A D)ᵒᵖ ⥤
      (DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat A)) :=
  Localization.lift (moduleResolutionHomSourceFunctor A D R)
    (moduleResolutionHomSourceFunctor_inverts A D R) (moduleToDerived A D).op

instance moduleResolutionDerivedHomBifunctor_lifting
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    Localization.Lifting (moduleToDerived A D).op (moduleQuasiIso A D).op
      (moduleResolutionHomSourceFunctor A D R) (moduleResolutionDerivedHomBifunctor A D R) :=
  Localization.liftingLift (moduleResolutionHomSourceFunctor A D R)
    (moduleResolutionHomSourceFunctor_inverts A D R) (moduleToDerived A D).op

def moduleResolutionDerivedHomBifunctor_fac
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    (moduleToDerived A D).op ⋙ moduleResolutionDerivedHomBifunctor A D R ≅
      moduleResolutionHomSourceFunctor A D R :=
  Localization.fac (moduleResolutionHomSourceFunctor A D R)
    (moduleResolutionHomSourceFunctor_inverts A D R) (moduleToDerived A D).op

def moduleResolutionDerivedHomBifunctorComputation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (M N : ModuleCategory A D) :
    ((moduleResolutionDerivedHomBifunctor A D R).obj (op ((moduleToDerived A D).obj M))).obj
        ((moduleToDerived A D).obj N) ≅
      DerivedCategory.Q.obj ((R M).obj ⟶[Complex A] N) :=
  ((moduleResolutionDerivedHomBifunctor_fac A D R).app (op M)).app
    ((moduleToDerived A D).obj N) ≪≫ (R M).derivedHomComputation N

def moduleDerivedHomBifunctor :
    (DerivedModuleCategory A D)ᵒᵖ ⥤
      (DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat A)) :=
  moduleResolutionDerivedHomBifunctor A D (moduleCanonicalProjectiveResolution A D)

def moduleDerivedHomBifunctorResolutionComputation {M : ModuleCategory A D}
    (P : ModuleProjectiveResolution A D M) (N : ModuleCategory A D) :
    ((moduleDerivedHomBifunctor A D).obj (op ((moduleToDerived A D).obj M))).obj
        ((moduleToDerived A D).obj N) ≅ DerivedCategory.Q.obj (P.obj ⟶[Complex A] N) :=
  ((moduleResolutionDerivedHomBifunctor_fac A D
    (moduleCanonicalProjectiveResolution A D)).app (op M)).app ((moduleToDerived A D).obj N) ≪≫
      (P.derivedHomIso (moduleCanonicalProjectiveResolution A D M)).app
        ((moduleToDerived A D).obj N) ≪≫ P.derivedHomComputation N

end SerrePositivity.DifferentialGraded
