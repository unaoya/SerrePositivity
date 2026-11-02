module
public import SerrePositivity.DifferentialGraded.Derived.ResolutionFunctorChoice
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Pentagon
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # 固定左dg加群との導来tensor

指定quasiIso局所化から射影解像度をK(D)へ取り、既存tensor関手をK(A)、D(A)へ合成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma moduleTensorDerived_map_eq_of_homotopy_map_eq (L : LeftModule A D)
    {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : (moduleToHomotopy A D).map f = (moduleToHomotopy A D).map g) :
    DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D L).map f) =
      DerivedCategory.Q.map ((BalancedTensor.rightTensorFunctor A D L).map g) := by
  obtain ⟨ht⟩ := (moduleToHomotopy_map_eq_iff A D f g).1 h
  exact DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{u} A)
    (BalancedTensor.rightTensorMap_homotopy A D L ht).some

/-- 解像度族を指定した固定左加群との導来tensor。 -/
def moduleResolutionDerivedTensor
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (L : LeftModule A D) :
    DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A) :=
  moduleDerivedResolutionFunctor A D R ⋙
    BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh

def moduleTensorHomotopyComputation (L : LeftModule A D) (M : ModuleCategory A D) :
    (BalancedTensor.rightTensorHomotopyFunctor A D L).obj ((moduleToHomotopy A D).obj M) ≅
      (_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).obj
        ((BalancedTensor.rightTensorFunctor A D L).obj M) :=
  eqToIso (congrArg (fun F => F.obj M) (BalancedTensor.rightTensorHomotopyFunctor_fac A D L))

/-- 主導来圏の対象での、実際の射影解像度による計算。 -/
def moduleResolutionDerivedTensorComputation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    (L : LeftModule A D) (M : ModuleCategory A D) :
    (moduleResolutionDerivedTensor A D R L).obj ((moduleToDerived A D).obj M) ≅
      DerivedCategory.Q.obj ((BalancedTensor.rightTensorFunctor A D L).obj (R M).obj) :=
  (BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh).mapIso
      (moduleDerivedResolutionComputation A D R M) ≪≫
    DerivedCategory.Qh.mapIso (moduleTensorHomotopyComputation A D L (R M).obj) ≪≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app
        ((BalancedTensor.rightTensorFunctor A D L).obj (R M).obj)

/-- 既存の標準semifree解像度から作る固定左加群との導来tensor。 -/
def moduleDerivedTensorRight (L : LeftModule A D) :
    DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A) :=
  moduleResolutionDerivedTensor A D (moduleCanonicalProjectiveResolution A D) L

/-- 任意の二つの解像度族から作った導来tensorは自然同型。 -/
def moduleResolutionDerivedTensorIso
    (R S : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (L : LeftModule A D) :
    moduleResolutionDerivedTensor A D R L ≅ moduleResolutionDerivedTensor A D S L :=
  Functor.isoWhiskerRight (moduleDerivedResolutionIso A D R S)
    (BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh)

lemma moduleResolutionDerivedTensorIso_self
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (L : LeftModule A D) :
    moduleResolutionDerivedTensorIso A D R R L = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh).map
    ((moduleDerivedResolutionIso A D R R).hom.app X) = 𝟙 _
  rw [moduleDerivedResolutionIso_self]
  exact (BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh).map_id _

lemma moduleResolutionDerivedTensorIso_trans
    (R S T : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (L : LeftModule A D) :
    moduleResolutionDerivedTensorIso A D R S L ≪≫ moduleResolutionDerivedTensorIso A D S T L =
      moduleResolutionDerivedTensorIso A D R T L := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh).map
      ((moduleDerivedResolutionIso A D R S).hom.app X) ≫
    (BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh).map
      ((moduleDerivedResolutionIso A D S T).hom.app X) = _
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg (fun f =>
    (BalancedTensor.rightTensorHomotopyFunctor A D L ⋙ DerivedCategory.Qh).map f)
    (NatTrans.congr_app (congrArg Iso.hom (moduleDerivedResolutionIso_trans A D R S T)) X)

end SerrePositivity.DifferentialGraded
