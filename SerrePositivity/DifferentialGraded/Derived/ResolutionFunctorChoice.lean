module
public import SerrePositivity.DifferentialGraded.Derived.ResolutionFunctor

/-! # 射影解像度関手の選択独立性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleResolutionHomotopyIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomotopyFunctor A D R ≅ moduleResolutionHomotopyFunctor A D S :=
  NatIso.ofComponents (fun M => by
    have := (R M).comparison_isIso_homotopy (S M)
    exact asIso ((moduleToHomotopy A D).map ((R M).comparison (S M)))) (by
      intro M N f
      exact (R M).lift_comparison_naturality (S M) (R N) (S N) f)

lemma moduleResolutionHomotopyIso_hom_app
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (moduleResolutionHomotopyIso A D R S).hom.app M =
      (moduleToHomotopy A D).map ((R M).comparison (S M)) := rfl

lemma moduleResolutionHomotopyIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomotopyIso A D R R = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simpa only [moduleResolutionHomotopyIso_hom_app, Iso.refl_hom, NatTrans.id_app,
    moduleResolutionHomotopyFunctor] using
    (R M).comparison_self

lemma moduleResolutionHomotopyIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomotopyIso A D R S ≪≫ moduleResolutionHomotopyIso A D S T =
      moduleResolutionHomotopyIso A D R T := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simpa only [Iso.trans_hom, NatTrans.comp_app, moduleResolutionHomotopyIso_hom_app] using
    (R M).comparison_comp (S M) (T M)

def moduleDerivedResolutionIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleDerivedResolutionFunctor A D R ≅ moduleDerivedResolutionFunctor A D S :=
  Localization.liftNatIso (moduleToDerived A D) (moduleQuasiIso A D)
    (moduleResolutionHomotopyFunctor A D R) (moduleResolutionHomotopyFunctor A D S)
    (moduleDerivedResolutionFunctor A D R) (moduleDerivedResolutionFunctor A D S)
    (moduleResolutionHomotopyIso A D R S)

lemma moduleDerivedResolutionIso_hom_app
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (moduleDerivedResolutionIso A D R S).hom.app ((moduleToDerived A D).obj M) =
      (moduleDerivedResolutionFunctor_fac A D R).hom.app M ≫
        (moduleResolutionHomotopyIso A D R S).hom.app M ≫
          (moduleDerivedResolutionFunctor_fac A D S).inv.app M :=
  Localization.liftNatTrans_app (moduleToDerived A D) (moduleQuasiIso A D)
    (moduleResolutionHomotopyFunctor A D R) (moduleResolutionHomotopyFunctor A D S)
    (moduleDerivedResolutionFunctor A D R) (moduleDerivedResolutionFunctor A D S)
    (moduleResolutionHomotopyIso A D R S).hom M

lemma moduleDerivedResolutionIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleDerivedResolutionIso A D R R = Iso.refl _ := by
  apply Iso.ext
  change Localization.liftNatTrans (moduleToDerived A D) (moduleQuasiIso A D)
    (moduleResolutionHomotopyFunctor A D R) (moduleResolutionHomotopyFunctor A D R)
    (moduleDerivedResolutionFunctor A D R) (moduleDerivedResolutionFunctor A D R)
    (moduleResolutionHomotopyIso A D R R).hom = 𝟙 _
  rw [moduleResolutionHomotopyIso_self, Iso.refl_hom, Localization.liftNatTrans_id]

lemma moduleDerivedResolutionIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleDerivedResolutionIso A D R S ≪≫ moduleDerivedResolutionIso A D S T =
      moduleDerivedResolutionIso A D R T := by
  apply Iso.ext
  change Localization.liftNatTrans (moduleToDerived A D) (moduleQuasiIso A D)
    (moduleResolutionHomotopyFunctor A D R) (moduleResolutionHomotopyFunctor A D S)
    (moduleDerivedResolutionFunctor A D R) (moduleDerivedResolutionFunctor A D S)
    (moduleResolutionHomotopyIso A D R S).hom ≫
    Localization.liftNatTrans (moduleToDerived A D) (moduleQuasiIso A D)
      (moduleResolutionHomotopyFunctor A D S) (moduleResolutionHomotopyFunctor A D T)
      (moduleDerivedResolutionFunctor A D S) (moduleDerivedResolutionFunctor A D T)
      (moduleResolutionHomotopyIso A D S T).hom =
    Localization.liftNatTrans (moduleToDerived A D) (moduleQuasiIso A D)
      (moduleResolutionHomotopyFunctor A D R) (moduleResolutionHomotopyFunctor A D T)
      (moduleDerivedResolutionFunctor A D R) (moduleDerivedResolutionFunctor A D T)
      (moduleResolutionHomotopyIso A D R T).hom
  rw [Localization.comp_liftNatTrans]
  exact congrArg (fun a => Localization.liftNatTrans (moduleToDerived A D) (moduleQuasiIso A D)
    (moduleResolutionHomotopyFunctor A D R) (moduleResolutionHomotopyFunctor A D T)
    (moduleDerivedResolutionFunctor A D R) (moduleDerivedResolutionFunctor A D T) a)
    (congrArg Iso.hom (moduleResolutionHomotopyIso_trans A D R S T))

end SerrePositivity.DifferentialGraded
