module
public import SerrePositivity.DifferentialGraded.Derived.TensorBifunctor
public import SerrePositivity.DifferentialGraded.Derived.TensorChoiceLeft

/-! # 両変数導来tensorの解像度族選択独立性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

def moduleResolutionDerivedTensorBifunctorFacIso
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    leftModuleToDerived A D ⋙ moduleResolutionDerivedTensorBifunctor A D R ≅
      moduleResolutionDerivedTensorLeftFunctor A D R :=
  eqToIso (moduleResolutionDerivedTensorBifunctor_fac A D R)

instance moduleResolutionDerivedTensorBifunctor_lifting
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    Localization.Lifting (leftModuleToDerived A D) (leftModuleQuasiIso A D)
      (moduleResolutionDerivedTensorLeftFunctor A D R)
      (moduleResolutionDerivedTensorBifunctor A D R) :=
  ⟨moduleResolutionDerivedTensorBifunctorFacIso A D R⟩

/-- 両変数を局所化したtensor双関手の、解像度族変更に対する自然同型。 -/
def moduleResolutionDerivedTensorBifunctorIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedTensorBifunctor A D R ≅ moduleResolutionDerivedTensorBifunctor A D S :=
  Localization.liftNatIso (leftModuleToDerived A D) (leftModuleQuasiIso A D)
    (moduleResolutionDerivedTensorLeftFunctor A D R) (moduleResolutionDerivedTensorLeftFunctor A
      D S)
    (moduleResolutionDerivedTensorBifunctor A D R) (moduleResolutionDerivedTensorBifunctor A D S)
    (moduleResolutionDerivedTensorLeftIso A D R S)

lemma moduleResolutionDerivedTensorBifunctorIso_hom_app
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : LeftModuleCategory A
      D) :
    (moduleResolutionDerivedTensorBifunctorIso A D R S).hom.app ((leftModuleToDerived A D).obj M) =
      (moduleResolutionDerivedTensorBifunctorFacIso A D R).hom.app M ≫
        (moduleResolutionDerivedTensorLeftIso A D R S).hom.app M ≫
          (moduleResolutionDerivedTensorBifunctorFacIso A D S).inv.app M :=
  Localization.liftNatTrans_app (leftModuleToDerived A D) (leftModuleQuasiIso A D)
    (moduleResolutionDerivedTensorLeftFunctor A D R) (moduleResolutionDerivedTensorLeftFunctor A
      D S)
    (moduleResolutionDerivedTensorBifunctor A D R) (moduleResolutionDerivedTensorBifunctor A D S)
    (moduleResolutionDerivedTensorLeftIso A D R S).hom M

lemma moduleResolutionDerivedTensorBifunctorIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedTensorBifunctorIso A D R R = Iso.refl _ := by
  apply Iso.ext
  change Localization.liftNatTrans (leftModuleToDerived A D) (leftModuleQuasiIso A D)
    (moduleResolutionDerivedTensorLeftFunctor A D R) (moduleResolutionDerivedTensorLeftFunctor A
      D R)
    (moduleResolutionDerivedTensorBifunctor A D R) (moduleResolutionDerivedTensorBifunctor A D R)
    (moduleResolutionDerivedTensorLeftIso A D R R).hom = 𝟙 _
  rw [moduleResolutionDerivedTensorLeftIso_self, Iso.refl_hom, Localization.liftNatTrans_id]

lemma moduleResolutionDerivedTensorBifunctorIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedTensorBifunctorIso A D R S ≪≫
      moduleResolutionDerivedTensorBifunctorIso A D S T =
      moduleResolutionDerivedTensorBifunctorIso A D R T := by
  apply Iso.ext
  change Localization.liftNatTrans (leftModuleToDerived A D) (leftModuleQuasiIso A D)
    (moduleResolutionDerivedTensorLeftFunctor A D R) (moduleResolutionDerivedTensorLeftFunctor A
      D S)
    (moduleResolutionDerivedTensorBifunctor A D R) (moduleResolutionDerivedTensorBifunctor A D S)
    (moduleResolutionDerivedTensorLeftIso A D R S).hom ≫
    Localization.liftNatTrans (leftModuleToDerived A D) (leftModuleQuasiIso A D)
      (moduleResolutionDerivedTensorLeftFunctor A D S) (moduleResolutionDerivedTensorLeftFunctor
        A D T)
      (moduleResolutionDerivedTensorBifunctor A D S) (moduleResolutionDerivedTensorBifunctor A D T)
      (moduleResolutionDerivedTensorLeftIso A D S T).hom =
    Localization.liftNatTrans (leftModuleToDerived A D) (leftModuleQuasiIso A D)
      (moduleResolutionDerivedTensorLeftFunctor A D R) (moduleResolutionDerivedTensorLeftFunctor
        A D T)
      (moduleResolutionDerivedTensorBifunctor A D R) (moduleResolutionDerivedTensorBifunctor A D T)
      (moduleResolutionDerivedTensorLeftIso A D R T).hom
  rw [Localization.comp_liftNatTrans]
  exact congrArg (fun a => Localization.liftNatTrans (leftModuleToDerived A D)
    (leftModuleQuasiIso A D)
    (moduleResolutionDerivedTensorLeftFunctor A D R) (moduleResolutionDerivedTensorLeftFunctor A
      D T)
    (moduleResolutionDerivedTensorBifunctor A D R) (moduleResolutionDerivedTensorBifunctor A D T) a)
    (congrArg Iso.hom (moduleResolutionDerivedTensorLeftIso_trans A D R S T))


end SerrePositivity.DifferentialGraded
