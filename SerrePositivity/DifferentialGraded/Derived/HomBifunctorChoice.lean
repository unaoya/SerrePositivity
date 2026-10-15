module
public import SerrePositivity.DifferentialGraded.Derived.HomBifunctor

/-! # 解像度族を替えた導来Hom双関手の自然同型とcocycle条件 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

def moduleResolutionHomSourceIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomSourceFunctor A D R ≅ moduleResolutionHomSourceFunctor A D S :=
  NatIso.ofComponents (fun X => (S X.unop).derivedHomIso (R X.unop)) (by
    intro X Y f
    let P := S Y.unop
    let Q := R Y.unop
    let U := S X.unop
    let V := R X.unop
    change moduleDerivedHomOutPrecomp A D Q.projective V.projective (Q.lift V f.unop) ≫
      moduleDerivedHomOutPrecomp A D P.projective Q.projective (P.comparison Q) =
        moduleDerivedHomOutPrecomp A D U.projective V.projective (U.comparison V) ≫
          moduleDerivedHomOutPrecomp A D P.projective U.projective (P.lift U f.unop)
    rw [← moduleDerivedHomOutPrecomp_comp, ← moduleDerivedHomOutPrecomp_comp]
    apply moduleDerivedHomOutPrecomp_eq_of_homotopy_map_eq A D P.projective V.projective
    exact ((moduleToHomotopy A D).map_comp _ _).trans
      ((P.lift_comparison_naturality Q U V f.unop).symm.trans
        ((moduleToHomotopy A D).map_comp _ _).symm))

lemma moduleResolutionHomSourceIso_app
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (X : (ModuleCategory A D)ᵒᵖ) :
    (moduleResolutionHomSourceIso A D R S).app X =
      (S X.unop).derivedHomIso (R X.unop) := rfl

lemma moduleResolutionHomSourceIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomSourceIso A D R R = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change ((R X.unop).derivedHomIso (R X.unop)).hom = 𝟙 _
  rw [ModuleProjectiveResolution.derivedHomIso_self]
  rfl

lemma moduleResolutionHomSourceIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomSourceIso A D R S ≪≫ moduleResolutionHomSourceIso A D S T =
      moduleResolutionHomSourceIso A D R T := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change ((S X.unop).derivedHomIso (R X.unop)).hom ≫
    ((T X.unop).derivedHomIso (S X.unop)).hom =
      ((T X.unop).derivedHomIso (R X.unop)).hom
  exact congrArg Iso.hom ((T X.unop).derivedHomIso_trans (S X.unop) (R X.unop))

def moduleResolutionDerivedHomBifunctorIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedHomBifunctor A D R ≅ moduleResolutionDerivedHomBifunctor A D S :=
  Localization.liftNatIso (moduleToDerived A D).op (moduleQuasiIso A D).op
    (moduleResolutionHomSourceFunctor A D R) (moduleResolutionHomSourceFunctor A D S)
    (moduleResolutionDerivedHomBifunctor A D R) (moduleResolutionDerivedHomBifunctor A D S)
    (moduleResolutionHomSourceIso A D R S)

lemma moduleResolutionDerivedHomBifunctorIso_app
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (moduleResolutionDerivedHomBifunctorIso A D R S).hom.app (op ((moduleToDerived A D).obj M)) =
      (moduleResolutionDerivedHomBifunctor_fac A D R).hom.app (op M) ≫
        (moduleResolutionHomSourceIso A D R S).hom.app (op M) ≫
          (moduleResolutionDerivedHomBifunctor_fac A D S).inv.app (op M) :=
  Localization.liftNatTrans_app (moduleToDerived A D).op (moduleQuasiIso A D).op
    (moduleResolutionHomSourceFunctor A D R) (moduleResolutionHomSourceFunctor A D S)
    (moduleResolutionDerivedHomBifunctor A D R) (moduleResolutionDerivedHomBifunctor A D S)
    (moduleResolutionHomSourceIso A D R S).hom (op M)

lemma moduleResolutionDerivedHomBifunctorIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedHomBifunctorIso A D R R = Iso.refl _ := by
  apply Iso.ext
  change Localization.liftNatTrans (moduleToDerived A D).op (moduleQuasiIso A D).op
    (moduleResolutionHomSourceFunctor A D R) (moduleResolutionHomSourceFunctor A D R)
    (moduleResolutionDerivedHomBifunctor A D R) (moduleResolutionDerivedHomBifunctor A D R)
    (moduleResolutionHomSourceIso A D R R).hom = 𝟙 _
  rw [moduleResolutionHomSourceIso_self, Iso.refl_hom, Localization.liftNatTrans_id]

lemma moduleResolutionDerivedHomBifunctorIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedHomBifunctorIso A D R S ≪≫
      moduleResolutionDerivedHomBifunctorIso A D S T =
        moduleResolutionDerivedHomBifunctorIso A D R T := by
  apply Iso.ext
  change Localization.liftNatTrans (moduleToDerived A D).op (moduleQuasiIso A D).op
    (moduleResolutionHomSourceFunctor A D R) (moduleResolutionHomSourceFunctor A D S)
    (moduleResolutionDerivedHomBifunctor A D R) (moduleResolutionDerivedHomBifunctor A D S)
    (moduleResolutionHomSourceIso A D R S).hom ≫
      Localization.liftNatTrans (moduleToDerived A D).op (moduleQuasiIso A D).op
        (moduleResolutionHomSourceFunctor A D S) (moduleResolutionHomSourceFunctor A D T)
        (moduleResolutionDerivedHomBifunctor A D S) (moduleResolutionDerivedHomBifunctor A D T)
        (moduleResolutionHomSourceIso A D S T).hom =
    Localization.liftNatTrans (moduleToDerived A D).op (moduleQuasiIso A D).op
      (moduleResolutionHomSourceFunctor A D R) (moduleResolutionHomSourceFunctor A D T)
      (moduleResolutionDerivedHomBifunctor A D R) (moduleResolutionDerivedHomBifunctor A D T)
      (moduleResolutionHomSourceIso A D R T).hom
  rw [Localization.comp_liftNatTrans]
  exact congrArg
    (Localization.liftNatTrans (moduleToDerived A D).op (moduleQuasiIso A D).op
      (moduleResolutionHomSourceFunctor A D R) (moduleResolutionHomSourceFunctor A D T)
      (moduleResolutionDerivedHomBifunctor A D R) (moduleResolutionDerivedHomBifunctor A D T))
    (congrArg Iso.hom (moduleResolutionHomSourceIso_trans A D R S T))

def moduleDerivedHomBifunctorChoiceIso
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleDerivedHomBifunctor A D ≅ moduleResolutionDerivedHomBifunctor A D R :=
  moduleResolutionDerivedHomBifunctorIso A D (moduleCanonicalProjectiveResolution A D) R

end SerrePositivity.DifferentialGraded
