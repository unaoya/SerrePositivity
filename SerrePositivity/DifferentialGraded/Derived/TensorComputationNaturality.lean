module
public import SerrePositivity.DifferentialGraded.Derived.TensorResolutionComparison

/-! # 導来tensor計算の射と解像度比較に関する自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleTensorHomotopyComputation_naturality (L : LeftModule A D)
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (BalancedTensor.rightTensorHomotopyFunctor A D L).map ((moduleToHomotopy A D).map f) ≫
        (moduleTensorHomotopyComputation A D L N).hom =
      (moduleTensorHomotopyComputation A D L M).hom ≫
        (_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).map
          ((BalancedTensor.rightTensorFunctor A D L).map f) := by
  exact (eqToIso (BalancedTensor.rightTensorHomotopyFunctor_fac A D L)).hom.naturality f

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- K(D)上のtensorを、既存D(A)の具体的tensor値へ比較する。 -/
def moduleTensorDerivedHomotopyComputation (L : LeftModule A D) (M : ModuleCategory A D) :
    (BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh).obj
        ((moduleToHomotopy A D).obj M) ≅
      DerivedCategory.Q.obj ((BalancedTensor.rightTensorFunctor A D L).obj M) :=
  DerivedCategory.Qh.mapIso (moduleTensorHomotopyComputation A D L M) ≪≫
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app
      ((BalancedTensor.rightTensorFunctor A D L).obj M)

lemma moduleTensorDerivedHomotopyComputation_naturality (L : LeftModule A D)
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh).map
        ((moduleToHomotopy A D).map f) ≫
          (moduleTensorDerivedHomotopyComputation A D L N).hom =
      (moduleTensorDerivedHomotopyComputation A D L M).hom ≫
        DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D L).map f) := by
  have h := congrArg (fun g => DerivedCategory.Qh.map g)
    (moduleTensorHomotopyComputation_naturality A D L f)
  simp only [CategoryTheory.Functor.map_comp] at h
  dsimp only [moduleTensorDerivedHomotopyComputation, Iso.trans_hom, Functor.mapIso_hom,
    Functor.comp_map, Iso.app_hom]
  rw [← Category.assoc, h, Category.assoc,
    DerivedCategory.quotientCompQhIso_hom_naturality, Category.assoc]

/-- 解像度族の比較自然同型は具体的な比較射によるtensor計算と可換。 -/
lemma moduleResolutionDerivedTensorComputation_choice
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModule A D) (M : ModuleCategory A D) :
    (moduleResolutionDerivedTensorIso A D R S L).hom.app ((moduleToDerived A D).obj M) ≫
        (moduleResolutionDerivedTensorComputation A D S L M).hom =
      (moduleResolutionDerivedTensorComputation A D R L M).hom ≫
        (moduleProjectiveResolutionTensorIso A D (R M) (S M) L).hom := by
  let H := BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh
  change H.map ((moduleDerivedResolutionIso A D R S).hom.app
      ((moduleToDerived A D).obj M)) ≫
      (H.map ((moduleDerivedResolutionComputation A D S M).hom) ≫
        (moduleTensorDerivedHomotopyComputation A D L (S M).obj).hom) =
    (H.map ((moduleDerivedResolutionComputation A D R M).hom) ≫
      (moduleTensorDerivedHomotopyComputation A D L (R M).obj).hom) ≫
        DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D L).map
          ((R M).comparison (S M)))
  rw [moduleDerivedResolutionIso_hom_app]
  simp only [moduleDerivedResolutionComputation, moduleResolutionHomotopyIso_hom_app,
    CategoryTheory.Functor.map_comp, Category.assoc, Iso.app_hom]
  dsimp only [moduleResolutionHomotopyFunctor] at *
  rw [← Category.assoc (H.map ((moduleDerivedResolutionFunctor_fac A D S).inv.app M)),
    ← H.map_comp, Iso.inv_hom_id_app, H.map_id, Category.id_comp]
  exact congrArg (fun g => H.map ((moduleDerivedResolutionFunctor_fac A D R).hom.app M) ≫ g)
    (moduleTensorDerivedHomotopyComputation_naturality A D L ((R M).comparison (S M)))

end SerrePositivity.DifferentialGraded
