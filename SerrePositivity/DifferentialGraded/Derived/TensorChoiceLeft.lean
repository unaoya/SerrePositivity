module
public import SerrePositivity.DifferentialGraded.Derived.RightTensorLeftFunctor

/-! # 解像度族比較の左加群変数に関する自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 固定左加群での比較は左加群のすべての射に関して自然。 -/
def moduleResolutionDerivedTensorLeftIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedTensorLeftFunctor A D R ≅
      moduleResolutionDerivedTensorLeftFunctor A D S :=
  NatIso.ofComponents
    (fun L => moduleResolutionDerivedTensorIso A D R S (ForgetEnrichment.to (Complex A) L))
    (by
      intro L L' g
      apply NatTrans.ext
      funext X
      let τ : BalancedTensor.rightTensorHomotopyFunctor A D (ForgetEnrichment.to (Complex A) L) ⋙
          DerivedCategory.Qh ⟶
        BalancedTensor.rightTensorHomotopyFunctor A D (ForgetEnrichment.to (Complex A) L') ⋙
          DerivedCategory.Qh :=
        Functor.whiskerRight (BalancedTensor.rightTensorHomotopyLeftMap A D g) DerivedCategory.Qh
      change τ.app ((moduleDerivedResolutionFunctor A D R).obj X) ≫
          (BalancedTensor.rightTensorHomotopyFunctor A D
            (ForgetEnrichment.to (Complex A) L') ⋙ DerivedCategory.Qh).map
              ((moduleDerivedResolutionIso A D R S).hom.app X) =
        (BalancedTensor.rightTensorHomotopyFunctor A D
          (ForgetEnrichment.to (Complex A) L) ⋙ DerivedCategory.Qh).map
            ((moduleDerivedResolutionIso A D R S).hom.app X) ≫
              τ.app ((moduleDerivedResolutionFunctor A D S).obj X)
      exact (τ.naturality ((moduleDerivedResolutionIso A D R S).hom.app X)).symm)

lemma moduleResolutionDerivedTensorLeftIso_hom_app
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModuleCategory A D) :
    (moduleResolutionDerivedTensorLeftIso A D R S).hom.app L =
      (moduleResolutionDerivedTensorIso A D R S (ForgetEnrichment.to (Complex A) L)).hom := rfl

lemma moduleResolutionDerivedTensorLeftIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedTensorLeftIso A D R R = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext L
  change (moduleResolutionDerivedTensorIso A D R R
    (ForgetEnrichment.to (Complex A) L)).hom =
      𝟙 (moduleResolutionDerivedTensor A D R (ForgetEnrichment.to (Complex A) L))
  exact congrArg Iso.hom
    (moduleResolutionDerivedTensorIso_self A D R (ForgetEnrichment.to (Complex A) L))

lemma moduleResolutionDerivedTensorLeftIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionDerivedTensorLeftIso A D R S ≪≫ moduleResolutionDerivedTensorLeftIso A D S T =
      moduleResolutionDerivedTensorLeftIso A D R T := by
  apply Iso.ext
  apply NatTrans.ext
  funext L
  simpa only [Iso.trans_hom, NatTrans.comp_app, moduleResolutionDerivedTensorLeftIso_hom_app]
    using congrArg Iso.hom
      (moduleResolutionDerivedTensorIso_trans A D R S T (ForgetEnrichment.to (Complex A) L))

end SerrePositivity.DifferentialGraded
