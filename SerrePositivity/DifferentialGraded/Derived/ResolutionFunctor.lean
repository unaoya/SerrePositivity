module
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveResolutionLift

/-! # 指定局所化からK(D)への射影解像度関手

証明付きの解像度族を選び、射の持ち上げのK(D)での一意性を使って関手化する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 射影解像度族をK(D)に値を持つ関手として扱う。 -/
def moduleResolutionHomotopyFunctor
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    ModuleCategory A D ⥤ ModuleHomotopyCategory A D where
  obj M := (moduleToHomotopy A D).obj (R M).obj
  map {M N} f := (moduleToHomotopy A D).map ((R M).lift (R N) f)
  map_id M := (R M).lift_id
  map_comp {M N P} f g := ((R M).lift_comp (R N) (R P) f g).symm

lemma moduleResolutionHomotopyFunctor_inverts
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    (moduleQuasiIso A D).IsInvertedBy (moduleResolutionHomotopyFunctor A D R) := by
  intro M N f hf
  exact moduleHomotopicallyProjective_quasiIso_isIso_homotopy A D
    (R M).projective (R N).projective ((R M).lift (R N) f) ((R M).lift_quasiIso (R N) f hf)

/-- 指定quasiIso局所化から主K(D)への射影解像度関手。 -/
def moduleDerivedResolutionFunctor
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    DerivedModuleCategory A D ⥤ ModuleHomotopyCategory A D :=
  Localization.lift (moduleResolutionHomotopyFunctor A D R)
    (moduleResolutionHomotopyFunctor_inverts A D R) (moduleToDerived A D)

instance moduleDerivedResolutionFunctor_lifting
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    Localization.Lifting (moduleToDerived A D) (moduleQuasiIso A D)
      (moduleResolutionHomotopyFunctor A D R) (moduleDerivedResolutionFunctor A D R) :=
  Localization.liftingLift (moduleResolutionHomotopyFunctor A D R)
    (moduleResolutionHomotopyFunctor_inverts A D R) (moduleToDerived A D)

def moduleDerivedResolutionFunctor_fac
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleToDerived A D ⋙ moduleDerivedResolutionFunctor A D R ≅
      moduleResolutionHomotopyFunctor A D R :=
  Localization.fac (moduleResolutionHomotopyFunctor A D R)
    (moduleResolutionHomotopyFunctor_inverts A D R) (moduleToDerived A D)

def moduleDerivedResolutionComputation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (moduleDerivedResolutionFunctor A D R).obj ((moduleToDerived A D).obj M) ≅
      (moduleToHomotopy A D).obj (R M).obj :=
  (moduleDerivedResolutionFunctor_fac A D R).app M

end SerrePositivity.DifferentialGraded
